#include "structs/index_pool.h"

#include "os/memory.h"

#include "os/log.h"

// TPot: copy os_memory_alloc here to ease counting LoC
void* os_memory_alloc(size_t count, size_t size)
/*INTERNAL*/ //@ requires count * size <= SIZE_MAX;
/*INTERNAL*/ /*@ ensures chars(result, count * size, ?cs) &*& true == all_eq(cs, 0) &*& result + count * size <= (char*) UINTPTR_MAX &*&
/*INTERNAL*/	    result != NULL &*& (size_t) result % (size + CACHE_LINE_SIZE - (size % CACHE_LINE_SIZE)) == 0; @*/
/*INTERNAL*/ //@ terminates;
{ 
	// ...
	// We don't count the body of this function.
}

// The odd use of fixpoints for seemingly-simple things such as nth_eq is required for forall_ to work properly;
// in general, only expressions that are direct arguments to calls can be "trigger" terms for forall_ expansion,
// see VeriFast's examples/fm2012/problem1-alternative.c

struct index_pool {
	time_t* timestamps;
	size_t size;
	time_t expiration_time;
	size_t last_borrowed_index;
};

/* SPEC */ /*SYNTAX*/ /*@
/* SPEC */fixpoint bool idx_in_bounds<t>(size_t i, list<t> xs) { return 0 <= i && i < length(xs); }
/* SPEC */fixpoint bool nth_eq<t>(size_t i, list<t> xs, t x) { return nth(i, xs) == x; }

/* SPEC */ predicate poolp_raw(struct index_pool* pool; size_t size, time_t expiration_time, size_t last_borrowed_index, list<time_t> timestamps) =
/* SPEC */	struct_index_pool_padding(pool) &*&
/* SPEC */	pool->timestamps |-> ?raw_timestamps &*&
/* SPEC */	pool->size |-> size &*&
/* SPEC */	pool->expiration_time |-> expiration_time &*&
/* SPEC */	pool->last_borrowed_index |-> last_borrowed_index &*&
/* SPEC */	raw_timestamps[0..size] |-> timestamps;

/* SPEC */predicate poolp_truths(list<time_t> timestamps, list<pair<size_t, time_t> > items) =
/* SPEC */	true == ghostmap_distinct(items) &*&
/* SPEC */	forall_(size_t k; (idx_in_bounds(k, timestamps) && !nth_eq(k, timestamps, TIME_MAX)) == ghostmap_has(items, k)) &*&
/* SPEC */	forall_(size_t k; !ghostmap_has(items, k) || ghostmap_get(items, k) == some(nth(k, timestamps)));

/* SPEC */predicate poolp(struct index_pool* pool, size_t size, time_t expiration_time, list<pair<size_t, time_t> > items) =
/* SPEC */	poolp_raw(pool, size, expiration_time, ?last_borrowed_index, ?timestamps) &*&
/* SPEC */	poolp_truths(timestamps, items) &*&
/* SPEC */ last_borrowed_index <= size;
/* SPEC */ /*SYNTAX*/ @*/

         /*@
/* PROOF */lemma void forall_eq_nth<t>(list<t> lst, t item)
/* PROOF */requires true == all_eq(lst, item);
/* PROOF */ensures forall_(int n; n < 0 || n >= length(lst) || nth(n, lst) == item);
/* PROOF */ /*SYNTAX*/ {
/* PROOF */for (int k = 0; k < length(lst); k++)
/* PROOF */	invariant 0 <= k &*& k <= length(lst) &*& forall_(int n; n < 0 || n >= k || nth(n, lst) == item);
/* PROOF */	decreases length(lst) - k;
/* PROOF */	/*SYNTAX*/ {
/* PROOF */		all_eq_nth(lst, item, k);
/* PROOF */	/*SYNTAX*/ }
/* PROOF */ /*SYNTAX*/ }

/* PROOF */lemma void forall_nth_unchanged<t>(int idx, t x, list<t> xs)
/* PROOF */requires emp;
/* PROOF */ensures forall_(int other; nth(other, xs) == nth(other, update(idx, x, xs)) || idx == other);
{/* PROOF */ /*SYNTAX*/ 
/* PROOF */	switch (xs) {
/* PROOF */		case nil:
/* PROOF */		case cons(h, t):
/* PROOF */			forall_nth_unchanged(idx - 1, x, t);
/* PROOF */	} /*SYNTAX*/ 
/* PROOF */} /*SYNTAX*/ 

/* PROOF */lemma void truths_update_HACK(list<pair<size_t, time_t> > items, list<time_t> timestamps, size_t index)
/* PROOF */requires forall_(size_t k; ((idx_in_bounds(k, timestamps) && !nth_eq(k, timestamps, TIME_MAX)) == ghostmap_has(items, k)) || k == index) &*&
/* PROOF */	 (idx_in_bounds(index, timestamps) && !nth_eq(index, timestamps, TIME_MAX)) == ghostmap_has(items, index);
/* PROOF */ensures forall_(size_t k; (idx_in_bounds(k, timestamps) && !nth_eq(k, timestamps, TIME_MAX)) == ghostmap_has(items, k));
/* PROOF */{ /*SYNTAX*/ 
	// For some reason VeriFast can figure it out on its own only when in a lemma.
/* PROOF */} /*SYNTAX*/ 
/* PROOF */lemma void truths_update(list<pair<size_t, time_t> > items, size_t index, time_t time)
/* PROOF */requires poolp_truths(?timestamps, items) &*&
/* PROOF */	 true == idx_in_bounds(index, timestamps);
/* PROOF */ensures poolp_truths(update(index, time, timestamps), time == TIME_MAX ? ghostmap_remove(items, index) : ghostmap_set(items, index, time));
/* PROOF */{ /*SYNTAX*/ 
/* PROOF */	open poolp_truths(timestamps, items);
/* PROOF */	forall_nth_unchanged(index, time, timestamps);
/* PROOF */	ghostmap_get_none_after_remove(items, index);
/* PROOF */	list<pair<size_t, time_t> > result = time == TIME_MAX ? ghostmap_remove(items, index) : ghostmap_set(items, index, time);
/* PROOF */	truths_update_HACK(result,  update(index, time, timestamps), index);
/* PROOF */	close poolp_truths(update(index, time, timestamps), result);
/* PROOF */} /*SYNTAX*/ 
		@*/

struct index_pool* index_pool_alloc(size_t size, time_t expiration_time)
/* SPEC *//*@ requires size * sizeof(time_t) <= SIZE_MAX; @*/
/* SPEC *//*@ ensures poolp(result, size, expiration_time, nil); @*/
/* SPEC *//*@ terminates; @*/
{
#ifdef REPLACE_OS_ALLOC_WITH_MALLOC
	struct index_pool* pool = malloc(1 * sizeof(struct index_pool));
	//@ close_struct(pool);
	pool->timestamps = malloc(size * sizeof(time_t));
#else
	struct index_pool* pool = (struct index_pool*) os_memory_alloc(1, sizeof(struct index_pool));
	/*PREDICATE*/ //@ close_struct_zero(pool);
	pool->timestamps = (time_t*) os_memory_alloc(size, sizeof(time_t));
#endif
	pool->size = size;
	pool->expiration_time = expiration_time;

	for (size_t n = size; n > 0; n--)
/* LOOP */	/*@ invariant pool->timestamps |-> ?raw_timestamps &*&
/* LOOP */		      chars((char*) raw_timestamps, n * sizeof(time_t), _) &*&
/* LOOP */		      raw_timestamps[n..size] |-> ?timestamps &*&
/* LOOP */  		      true == all_eq(timestamps, TIME_MAX); @*/
/*PROOF*/	//@ decreases n;
	{
/* PROOF */		//@ chars_split((char*) raw_timestamps, (n - 1) * sizeof(time_t));
/* PROOF */		//@ chars_to_integer_(raw_timestamps + n - 1, sizeof(time_t), TIME_MIN != 0);
		pool->timestamps[n - 1] = TIME_MAX;
	}

/* PROOF */	//@ assert pool->timestamps |-> ?raw_timestamps;
/* PROOF */	//@ assert raw_timestamps[0..size] |-> ?timestamps;
/* PROOF */	//@ forall_eq_nth(timestamps, TIME_MAX);
	/*PREDICATE*/ //@ close poolp_truths(timestamps, nil);
	/*PREDICATE*/ //@ close poolp(pool, size, expiration_time, nil);
	return pool;
}

		/*@ 
/* PROOF */lemma void pool_items_implication_tail(list<pair<size_t, time_t> > items, list<time_t> timestamps, time_t time, time_t exp_time)
/* PROOF */requires items == cons(?h, ?t) &*&
/* PROOF */	 true == ghostmap_distinct(items) &*&
/* PROOF */	 forall_(size_t k; !ghostmap_has(items, k) || (ghostmap_get(items, k) == some(nth(k, timestamps))));
/* PROOF */ensures forall_(size_t k; !ghostmap_has(t, k) || (ghostmap_get(t, k) == some(nth(k, timestamps))));
/* PROOF */{ /*SYNTAX*/ 
/* PROOF */	assert h == pair(?hk, ?hv);
/* PROOF */	assert !ghostmap_has(t, hk);
/* PROOF */} /*SYNTAX*/ 

/* PROOF */lemma void pool_items_young_forall_to_ghostmap(list<pair<size_t, time_t> > items, list<time_t> timestamps, time_t time, time_t exp_time)
/* PROOF */requires true == ghostmap_distinct(items) &*&
/* PROOF */	 forall_(size_t k; !ghostmap_has(items, k) || (ghostmap_get(items, k) == some(nth(k, timestamps)))) &*&
/* PROOF */	 forall_(size_t k; !ghostmap_has(items, k) || (time < exp_time || time - exp_time <= nth(k, timestamps)));
/* PROOF */ensures true == ghostmap_forall(items, (pool_young)(time, exp_time));
/* PROOF */{ /*SYNTAX*/ 
/* PROOF */	switch (items) {
/* PROOF */		case nil:
/* PROOF */		case cons(h, t):
/* PROOF */			assert h == pair(?hk, ?hv);
/* PROOF */			pool_items_implication_tail(items, timestamps, time, exp_time);
/* PROOF */			pool_items_young_forall_to_ghostmap(t, timestamps, time, exp_time);
/* PROOF */			assert ghostmap_get(items, hk) == some(hv);
/* PROOF */	} /*SYNTAX*/ 
/* PROOF */} /*SYNTAX*/ 
	@*/ 

bool index_pool_borrow(struct index_pool* pool, time_t time, size_t* out_index, bool* out_used)
/* SPEC *//*@ requires poolp(pool, ?size, ?exp_time, ?items) &*&
/* SPEC */	     time != TIME_MAX &*&
/* SPEC */	     *out_index |-> _ &*&
/* SPEC */	     *out_used |-> _; @*/
/* SPEC *//*@ ensures *out_index |-> ?index &*&
/* SPEC */	    *out_used |-> ?used &*&
/* SPEC */	    (length(items) == size ? (ghostmap_forall(items, (pool_young)(time, exp_time)) ? result == false
/* SPEC */											   : (result == true &*& used == true))
/* SPEC */				   : result == true) &*&
/* SPEC */	    result ? poolp(pool, size, exp_time, ghostmap_set(items, index, time)) &*&
/* SPEC */		     index < size &*&
/* SPEC */		     (used ? (ghostmap_get(items, index) == some(?old) &*&
/* SPEC */			      false == pool_young(time, exp_time, index, old))
/* SPEC */			   : (ghostmap_get(items, index) == none))
/* SPEC */		   : poolp(pool, size, exp_time, items); @*/
/* SPEC *//*@ terminates; @*/
{
	// Optimization:
	// Instead of looping through the entire array from zero,
	// we keep track of the last index we borrowed and start from there next time.
	// This avoids O(N^2) performance when borrowing a bunch of stuff at startup.
	// Cloning the loop is the easiest way to do this from a verification perspective.

/*PREDICATE*/		//@ open poolp(pool, size, exp_time, items);
	// These three lines are required to avoid failures later...
/*PREDICATE*/		//@ open poolp_truths(?timestamps, items);
/*PREDICATE*/		//@ close poolp_truths(timestamps, items);
/* PROOF */	//@ assert poolp_raw(pool, size, exp_time, ?lbi, timestamps);
	for (size_t n = pool->last_borrowed_index; n < pool->size; n++)
/* LOOP */	/*@ invariant poolp_raw(pool, size, exp_time, lbi, timestamps) &*&
/* LOOP */		      poolp_truths(timestamps, items) &*&
/* LOOP */		      *out_index |-> _ &*&
/* LOOP */		      *out_used |-> _ &*&
/* LOOP */		      lbi <= size &*&
/* LOOP */		      forall_(size_t k; !(lbi <= k && k < n) || !nth_eq(k, timestamps, TIME_MAX)) &*&
/* LOOP */		      forall_(size_t k; !(lbi <= k && k < n) || (time < exp_time || time - exp_time <= nth(k, timestamps))); @*/
	/*PROOF*/ //@ decreases size - n;
	{
		if (pool->timestamps[n] == TIME_MAX) {
/* PROOF */			//@ ghostmap_array_max_size(items, size, n);
			pool->timestamps[n] = time;
			pool->last_borrowed_index = n;
			*out_index = n;
			*out_used = false;
/* PROOF */			//@ truths_update(items, n, time);
/*PREDICATE*/			//@ close poolp(pool, size, exp_time, ghostmap_set(items, n, time));
			os_debug("timestamp branch 1");
			return true;
		}
		if (time >= pool->expiration_time && time - pool->expiration_time > pool->timestamps[n]) {
/* PROOF */			//@ ghostmap_notpred_implies_notforall(items, (pool_young)(time, exp_time), n);
			pool->timestamps[n] = time;
			pool->last_borrowed_index = n;
			*out_index = n;
			*out_used = true;
/* PROOF */			//@ truths_update(items, n, time);
/*PREDICATE*/			//@ close poolp(pool, size, exp_time, ghostmap_set(items, n, time));
			os_debug("timestamp branch 2");
			return true;
		}
	}
	for (size_t n = 0; n < pool->last_borrowed_index; n++)
/* LOOP */	/*@ invariant poolp_raw(pool, size, exp_time, lbi, timestamps) &*&
/* LOOP */		      poolp_truths(timestamps, items) &*&
/* LOOP */		      *out_index |-> _ &*&
/* LOOP */	      *out_used |-> _ &*&
/* LOOP */		      forall_(size_t k; !(0 <= k && k < n) || !nth_eq(k, timestamps, TIME_MAX)) &*&
/* LOOP */		      forall_(size_t k; !(0 <= k && k < n) || (time < exp_time || time - exp_time <= nth(k, timestamps))); @*/
	/*PROOF*/ //@ decreases lbi - n;
	{
		if (pool->timestamps[n] == TIME_MAX) {
/* PROOF */			//@ ghostmap_array_max_size(items, size, n);
			pool->timestamps[n] = time;
			pool->last_borrowed_index = n;
			*out_index = n;
			*out_used = false;
/* PROOF */			//@ truths_update(items, n, time);
/*PREDICATE*/				//@ close poolp(pool, size, exp_time, ghostmap_set(items, n, time));
			os_debug("timestamp branch 3");
			return true;
		}
		if (time >= pool->expiration_time && time - pool->expiration_time > pool->timestamps[n]) {
/* PROOF */			//@ ghostmap_notpred_implies_notforall(items, (pool_young)(time, exp_time), n);
			pool->timestamps[n] = time;
			pool->last_borrowed_index = n;
			*out_index = n;
			*out_used = true;
/* PROOF */			//@ truths_update(items, n, time);
/* PREDICATE */			//@ close poolp(pool, size, exp_time, ghostmap_set(items, n, time));
			os_debug("timestamp branch 4");
			return true;
		}
	}
/* PREDICATE */	//@ open poolp_truths(timestamps, items);
/* PROOF *	//@ ghostmap_array_size(items, size);
/* PROOF *	//@ pool_items_young_forall_to_ghostmap(items, timestamps, time, exp_time);
/* PREDICATE */	//@ close poolp_truths(timestamps, items);
/* PREDICATE */	//@ close poolp(pool, size, exp_time, items);
	os_debug("timestamp branch 5");
	return false;
}

void index_pool_refresh(struct index_pool* pool, time_t time, size_t index)
/* SPEC */ /*@ requires poolp(pool, ?size, ?exp_time, ?items) &*&
/* SPEC */	     time != TIME_MAX &*&
/* SPEC */	     index < size; @*/
/* SPEC */ /*@ ensures poolp(pool, size, exp_time, ghostmap_set(items, index, time)); @*/
/* SPEC */ /*@ terminates; @*/
{
/* PREDICATE */	//@ open poolp(pool, size, exp_time, items);
	pool->timestamps[index] = time;
/* PROOF */	//@ truths_update(items, index, time);
/* PREDICATE */	//@ close poolp(pool, size, exp_time, ghostmap_set(items, index, time));
}

bool index_pool_used(struct index_pool* pool, time_t time, size_t index)
/* SPEC */ /*@ requires poolp(pool, ?size, ?exp_time, ?items); @*/
/* SPEC */ /*@ ensures poolp(pool, size, exp_time, items) &*&
/* SPEC */	    switch (ghostmap_get(items, index)) {
/* SPEC */	      case none: return result == false;
/* SPEC */	      case some(t): return result == pool_young(time, exp_time, 0, t);
/* SPEC */	    }; @*/ /*SYNTAX*/ 
/* SPEC */ /*@ terminates; @*/
{
/* PREDICATE */	//@ open poolp(pool, size, exp_time, items);
/* PREDICATE */	//@ open poolp_truths(?timestamps, items);
	if (index >= pool->size) {
/* PREDICATE */		//@ close poolp_truths(timestamps, items);
/* PREDICATE */		//@ close poolp(pool, size, exp_time, items);
		return false;
	}
	if (pool->timestamps[index] == TIME_MAX) {
/* PREDICATE */		//@ close poolp_truths(timestamps, items);
/* PREDICATE */		//@ close poolp(pool, size, exp_time, items);
		return false;
	}
	if (time >= pool->expiration_time && time - pool->expiration_time > pool->timestamps[index]) {
/* PREDICATE */		//@ close poolp_truths(timestamps, items);
/* PREDICATE */		//@ close poolp(pool, size, exp_time, items);
		return false;
	}
/* PREDICATE */	//@ close poolp_truths(timestamps, items);
/* PREDICATE */	//@ close poolp(pool, size, exp_time, items);
	return true;
}

void index_pool_return(struct index_pool* pool, size_t index)
/* SPEC */ /*@ requires poolp(pool, ?size, ?exp_time, ?items) &*&
	     index < size; @*/
/* SPEC */ /*@ ensures poolp(pool, size, exp_time, ghostmap_remove(items, index)); @*/
/* SPEC */ /*@ terminates; @*/
{
/* PREDICATE */	//@ open poolp(pool, size, exp_time, items);
	pool->timestamps[index] = TIME_MAX;
/* PROOF */	//@ truths_update(items, index, TIME_MAX);
/* PREDICATE */	//@ close poolp(pool, size, exp_time, ghostmap_remove(items, index));
}

