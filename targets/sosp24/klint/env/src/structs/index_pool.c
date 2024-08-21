#include "structs/index_pool.h"

#include "os/memory.h"

#include <tpot_annotations.h> // tpot_inv

// The odd use of fixpoints for seemingly-simple things such as nth_eq is required for forall_ to work properly;
// in general, only expressions that are direct arguments to calls can be "trigger" terms for forall_ expansion,
// see VeriFast's examples/fm2012/problem1-alternative.c

struct index_pool {
	time_t* timestamps;
	size_t size;
	time_t expiration_time;
	size_t last_borrowed_index;
};

/*LOOPINV*/ /*SYNTAX*/bool following_elems_zero(time_t *unused, int64_t j, size_t n, struct index_pool *pool) {
/*LOOPINV*/     if (j < n || j >= pool->size) return true;
/*LOOPINV*/     return pool->timestamps[j] == TIME_MAX;
/*LOOPINV*/ } /*SYNTAX*/
/*LOOPINV*/ /*SYNTAX*/bool loopinv_alloc(size_t *n_ptr, struct index_pool **pool_ptr) {
/*LOOPINV*/     size_t n = *n_ptr; struct index_pool *pool = *pool_ptr;
/*LOOPINV*/     return n > 0 && n <= pool->size &&
/*LOOPINV*/             forall_elem_(pool->timestamps, &following_elems_zero, n, pool);
/*LOOPINV*/ } /*SYNTAX*/
/*@
fixpoint bool idx_in_bounds<t>(size_t i, list<t> xs) { return 0 <= i && i < length(xs); }
fixpoint bool nth_eq<t>(size_t i, list<t> xs, t x) { return nth(i, xs) == x; }

predicate poolp_raw(struct index_pool* pool; size_t size, time_t expiration_time, size_t last_borrowed_index, list<time_t> timestamps) =
	struct_index_pool_padding(pool) &*&
	pool->timestamps |-> ?raw_timestamps &*&
	pool->size |-> size &*&
	pool->expiration_time |-> expiration_time &*&
	pool->last_borrowed_index |-> last_borrowed_index &*&
	raw_timestamps[0..size] |-> timestamps;

predicate poolp_truths(list<time_t> timestamps, list<pair<size_t, time_t> > items) =
	true == ghostmap_distinct(items) &*&
	forall_(size_t k; (idx_in_bounds(k, timestamps) && !nth_eq(k, timestamps, TIME_MAX)) == ghostmap_has(items, k)) &*&
	forall_(size_t k; !ghostmap_has(items, k) || ghostmap_get(items, k) == some(nth(k, timestamps)));

predicate poolp(struct index_pool* pool, size_t size, time_t expiration_time, list<pair<size_t, time_t> > items) =
	poolp_raw(pool, size, expiration_time, ?last_borrowed_index, ?timestamps) &*&
	poolp_truths(timestamps, items) &*&
	last_borrowed_index <= size;
@*/

/*@
lemma void forall_eq_nth<t>(list<t> lst, t item)
requires true == all_eq(lst, item);
ensures forall_(int n; n < 0 || n >= length(lst) || nth(n, lst) == item);
{
	for (int k = 0; k < length(lst); k++)
	invariant 0 <= k &*& k <= length(lst) &*& forall_(int n; n < 0 || n >= k || nth(n, lst) == item);
	decreases length(lst) - k;
	{
		all_eq_nth(lst, item, k);
	}
}

lemma void forall_nth_unchanged<t>(int idx, t x, list<t> xs)
requires emp;
ensures forall_(int other; nth(other, xs) == nth(other, update(idx, x, xs)) || idx == other);
{
	switch (xs) {
		case nil:
		case cons(h, t):
			forall_nth_unchanged(idx - 1, x, t);
	}
}

lemma void truths_update_HACK(list<pair<size_t, time_t> > items, list<time_t> timestamps, size_t index)
requires forall_(size_t k; ((idx_in_bounds(k, timestamps) && !nth_eq(k, timestamps, TIME_MAX)) == ghostmap_has(items, k)) || k == index) &*&
	 (idx_in_bounds(index, timestamps) && !nth_eq(index, timestamps, TIME_MAX)) == ghostmap_has(items, index);
ensures forall_(size_t k; (idx_in_bounds(k, timestamps) && !nth_eq(k, timestamps, TIME_MAX)) == ghostmap_has(items, k));
{
	// For some reason VeriFast can figure it out on its own only when in a lemma.
}
lemma void truths_update(list<pair<size_t, time_t> > items, size_t index, time_t time)
requires poolp_truths(?timestamps, items) &*&
	 true == idx_in_bounds(index, timestamps);
ensures poolp_truths(update(index, time, timestamps), time == TIME_MAX ? ghostmap_remove(items, index) : ghostmap_set(items, index, time));
{
	open poolp_truths(timestamps, items);
	forall_nth_unchanged(index, time, timestamps);
	ghostmap_get_none_after_remove(items, index);
	list<pair<size_t, time_t> > result = time == TIME_MAX ? ghostmap_remove(items, index) : ghostmap_set(items, index, time);
	truths_update_HACK(result,  update(index, time, timestamps), index);
	close poolp_truths(update(index, time, timestamps), result);
}
@*/

struct index_pool* index_pool_alloc(size_t size, time_t expiration_time)
/*@ requires size * sizeof(time_t) <= SIZE_MAX; @*/
/*@ ensures poolp(result, size, expiration_time, nil); @*/
/*@ terminates; @*/
{
	struct index_pool* pool = (struct index_pool*) os_memory_alloc(1, sizeof(struct index_pool));
	//@ close_struct_zero(pool);
	pool->timestamps = (time_t*) os_memory_alloc(size, sizeof(time_t));
	pool->size = size;
	pool->expiration_time = expiration_time;

	for (size_t n = size; n > 0; n--)
	/*@ invariant pool->timestamps |-> ?raw_timestamps &*&
		      chars((char*) raw_timestamps, n * sizeof(time_t), _) &*&
		      raw_timestamps[n..size] |-> ?timestamps &*&
		      true == all_eq(timestamps, TIME_MAX); @*/
	//@ decreases n;
	{
/*LOOPINV*/ _tpot_inv(&loopinv_alloc, &n, &pool, &n, sizeof(n), pool->timestamps, sizeof(time_t[size]));
		//@ chars_split((char*) raw_timestamps, (n - 1) * sizeof(time_t));
		//@ chars_to_integer_(raw_timestamps + n - 1, sizeof(time_t), TIME_MIN != 0);
		pool->timestamps[n - 1] = TIME_MAX;
	}

	//@ assert pool->timestamps |-> ?raw_timestamps;
	//@ assert raw_timestamps[0..size] |-> ?timestamps;
	//@ forall_eq_nth(timestamps, TIME_MAX);
	//@ close poolp_truths(timestamps, nil);
	//@ close poolp(pool, size, expiration_time, nil);
	return pool;
}

/*@
lemma void pool_items_implication_tail(list<pair<size_t, time_t> > items, list<time_t> timestamps, time_t time, time_t exp_time)
requires items == cons(?h, ?t) &*&
	 true == ghostmap_distinct(items) &*&
	 forall_(size_t k; !ghostmap_has(items, k) || (ghostmap_get(items, k) == some(nth(k, timestamps))));
ensures forall_(size_t k; !ghostmap_has(t, k) || (ghostmap_get(t, k) == some(nth(k, timestamps))));
{
	assert h == pair(?hk, ?hv);
	assert !ghostmap_has(t, hk);
}

lemma void pool_items_young_forall_to_ghostmap(list<pair<size_t, time_t> > items, list<time_t> timestamps, time_t time, time_t exp_time)
requires true == ghostmap_distinct(items) &*&
	 forall_(size_t k; !ghostmap_has(items, k) || (ghostmap_get(items, k) == some(nth(k, timestamps)))) &*&
	 forall_(size_t k; !ghostmap_has(items, k) || (time < exp_time || time - exp_time <= nth(k, timestamps)));
ensures true == ghostmap_forall(items, (pool_young)(time, exp_time));
{
	switch (items) {
		case nil:
		case cons(h, t):
			assert h == pair(?hk, ?hv);
			pool_items_implication_tail(items, timestamps, time, exp_time);
			pool_items_young_forall_to_ghostmap(t, timestamps, time, exp_time);
			assert ghostmap_get(items, hk) == some(hv);
	}
}
@*/

/*LOOPINV*/ bool loopinv_borrow(size_t *n_ptr, size_t *size_ptr) {/*SYNTAX*/ 
/*LOOPINV*/ 	size_t n = *n_ptr; size_t size = *size_ptr;
/*LOOPINV*/ 	return n >= 0 && n < size;
/*LOOPINV*/ }/*SYNTAX*/ 

bool index_pool_borrow(struct index_pool* pool, time_t time, size_t* out_index, bool* out_used)
/*@ requires poolp(pool, ?size, ?exp_time, ?items) &*&
	     time != TIME_MAX &*&
	     *out_index |-> _ &*&
	     *out_used |-> _; @*/
/*@ ensures *out_index |-> ?index &*&
	    *out_used |-> ?used &*&
	    (length(items) == size ? (ghostmap_forall(items, (pool_young)(time, exp_time)) ? result == false
											   : (result == true &*& used == true))
				   : result == true) &*&
	    result ? poolp(pool, size, exp_time, ghostmap_set(items, index, time)) &*&
		     index < size &*&
		     (used ? (ghostmap_get(items, index) == some(?old) &*&
			      false == pool_young(time, exp_time, index, old))
			   : (ghostmap_get(items, index) == none))
		   : poolp(pool, size, exp_time, items); @*/
/*@ terminates; @*/
{
	// Optimization:
	// Instead of looping through the entire array from zero,
	// we keep track of the last index we borrowed and start from there next time.
	// This avoids O(N^2) performance when borrowing a bunch of stuff at startup.
	// Cloning the loop is the easiest way to do this from a verification perspective.

	//@ open poolp(pool, size, exp_time, items);
	// These three lines are required to avoid failures later...
	//@ open poolp_truths(?timestamps, items);
	//@ close poolp_truths(timestamps, items);
	//@ assert poolp_raw(pool, size, exp_time, ?lbi, timestamps);
	for (size_t n = pool->last_borrowed_index; n < pool->size; n++)
	/*@ invariant poolp_raw(pool, size, exp_time, lbi, timestamps) &*&
		      poolp_truths(timestamps, items) &*&
		      *out_index |-> _ &*&
		      *out_used |-> _ &*&
		      lbi <= size &*&
		      forall_(size_t k; !(lbi <= k && k < n) || !nth_eq(k, timestamps, TIME_MAX)) &*&
		      forall_(size_t k; !(lbi <= k && k < n) || (time < exp_time || time - exp_time <= nth(k, timestamps))); @*/
	//@ decreases size - n;
	{
		/*LOOPINV*/ _tpot_inv(&loopinv_borrow, &n, &pool->size, &n, sizeof(n));

		if (pool->timestamps[n] == TIME_MAX) {
			//@ ghostmap_array_max_size(items, size, n);
			pool->timestamps[n] = time;
			pool->last_borrowed_index = n;
			*out_index = n;
			*out_used = false;
			//@ truths_update(items, n, time);
			//@ close poolp(pool, size, exp_time, ghostmap_set(items, n, time));
			return true;
		}
		if (time >= pool->expiration_time && time - pool->expiration_time > pool->timestamps[n]) {
			//@ ghostmap_notpred_implies_notforall(items, (pool_young)(time, exp_time), n);
			pool->timestamps[n] = time;
			pool->last_borrowed_index = n;
			*out_index = n;
			*out_used = true;
			//@ truths_update(items, n, time);
			//@ close poolp(pool, size, exp_time, ghostmap_set(items, n, time));
			return true;
		}
	}
	for (size_t n = 0; n < pool->last_borrowed_index; n++)
	/*@ invariant poolp_raw(pool, size, exp_time, lbi, timestamps) &*&
		      poolp_truths(timestamps, items) &*&
		      *out_index |-> _ &*&
		      *out_used |-> _ &*&
		      forall_(size_t k; !(0 <= k && k < n) || !nth_eq(k, timestamps, TIME_MAX)) &*&
		      forall_(size_t k; !(0 <= k && k < n) || (time < exp_time || time - exp_time <= nth(k, timestamps))); @*/
	//@ decreases lbi - n;
	{
		/*LOOPINV*/ _tpot_inv(&loopinv_borrow, &n, &pool->size, &n, sizeof(n));
		
		if (pool->timestamps[n] == TIME_MAX) {
			//@ ghostmap_array_max_size(items, size, n);
			pool->timestamps[n] = time;
			pool->last_borrowed_index = n;
			*out_index = n;
			*out_used = false;
			//@ truths_update(items, n, time);
			//@ close poolp(pool, size, exp_time, ghostmap_set(items, n, time));
			return true;
		}
		if (time >= pool->expiration_time && time - pool->expiration_time > pool->timestamps[n]) {
			//@ ghostmap_notpred_implies_notforall(items, (pool_young)(time, exp_time), n);
			pool->timestamps[n] = time;
			pool->last_borrowed_index = n;
			*out_index = n;
			*out_used = true;
			//@ truths_update(items, n, time);
			//@ close poolp(pool, size, exp_time, ghostmap_set(items, n, time));
			return true;
		}
	}
	//@ open poolp_truths(timestamps, items);
	//@ ghostmap_array_size(items, size);
	//@ pool_items_young_forall_to_ghostmap(items, timestamps, time, exp_time);
	//@ close poolp_truths(timestamps, items);
	//@ close poolp(pool, size, exp_time, items);
	return false;
}

void index_pool_refresh(struct index_pool* pool, time_t time, size_t index)
/*@ requires poolp(pool, ?size, ?exp_time, ?items) &*&
	     time != TIME_MAX &*&
	     index < size; @*/
/*@ ensures poolp(pool, size, exp_time, ghostmap_set(items, index, time)); @*/
/*@ terminates; @*/
{
	//@ open poolp(pool, size, exp_time, items);
	pool->timestamps[index] = time;
	//@ truths_update(items, index, time);
	//@ close poolp(pool, size, exp_time, ghostmap_set(items, index, time));
}

bool index_pool_used(struct index_pool* pool, time_t time, size_t index)
/*@ requires poolp(pool, ?size, ?exp_time, ?items); @*/
/*@ ensures poolp(pool, size, exp_time, items) &*&
	    switch (ghostmap_get(items, index)) {
	      case none: return result == false;
	      case some(t): return result == pool_young(time, exp_time, 0, t);
	    }; @*/
/*@ terminates; @*/
{
	//@ open poolp(pool, size, exp_time, items);
	//@ open poolp_truths(?timestamps, items);
	if (index >= pool->size) {
		//@ close poolp_truths(timestamps, items);
		//@ close poolp(pool, size, exp_time, items);
		return false;
	}
	if (pool->timestamps[index] == TIME_MAX) {
		//@ close poolp_truths(timestamps, items);
		//@ close poolp(pool, size, exp_time, items);
		return false;
	}
	if (time >= pool->expiration_time && time - pool->expiration_time > pool->timestamps[index]) {
		//@ close poolp_truths(timestamps, items);
		//@ close poolp(pool, size, exp_time, items);
		return false;
	}
	//@ close poolp_truths(timestamps, items);
	//@ close poolp(pool, size, exp_time, items);
	return true;
}

void index_pool_return(struct index_pool* pool, size_t index)
/*@ requires poolp(pool, ?size, ?exp_time, ?items) &*&
	     index < size; @*/
/*@ ensures poolp(pool, size, exp_time, ghostmap_remove(items, index)); @*/
/*@ terminates; @*/
{
	//@ open poolp(pool, size, exp_time, items);
	pool->timestamps[index] = TIME_MAX;
	//@ truths_update(items, index, TIME_MAX);
	//@ close poolp(pool, size, exp_time, ghostmap_remove(items, index));
}
