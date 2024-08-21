#include "spec_helpers.h"

/*SPECS*/ struct index_pool* pool;
/*SPECS*/ #define POOL_SIZE 1024

// --- invariants --- //
bool inv__pool() { // GLOBAL
    return names_obj(pool, struct index_pool) && pool->size == POOL_SIZE // GLOBAL
        && names_obj(pool->timestamps, time_t[pool->size]) // GLOBAL
        && (pool->last_borrowed_index < pool->size); // GLOBAL
} // GLOBAL // SYNTAX

// --- specs --- //
/*SPECS*/ void spec__borrow() {
/*SPECS*/     any(time_t, time);
/*SPECS*/     assume(time != TIME_MAX);

/*SPECS*/     size_t out_index; bool out_used;

/*SPECS*/     bool res = index_pool_borrow(pool, time, &out_index, &out_used);

/*SPECS*/     if (res) {
/*SPECS*/         assert(out_index < pool->size);
/*SPECS*/         // out_index is updated to _time_
/*SPECS*/         assert(pool->timestamps[out_index] == time);
/*SPECS*/         assert_unchanged_except__(pool->last_borrowed_index, pool->timestamps[out_index]);

/*SPECS*/         if (out_used) {
/*SPECS*/             // the index was previously expired
/*SPECS*/             assert_old(!pool_young(time, pool->expiration_time, out_index, pool->timestamps[out_index]));
/*SPECS*/         } else {
/*SPECS*/             // the index was previously not in use
/*SPECS*/             assert_old(pool->timestamps[out_index] == TIME_MAX);
/*SPECS*/         } /*SYNTAX*/
/*SPECS*/     } else {
/*SPECS*/         assert_unchanged();
/*SPECS*/     } /*SYNTAX*/
/*SPECS*/ } /*SYNTAX*/

/*SPECS*/ void spec__refresh() {
/*SPECS*/     any(time_t, time); any(size_t, index);

/*SPECS*/     assume(time != TIME_MAX);
/*SPECS*/     assume(index < pool->size);

/*SPECS*/     index_pool_refresh(pool, time, index);

/*SPECS*/     assert(pool->timestamps[index] == time);
/*SPECS*/     assert_unchanged_except_(pool->timestamps[index]);
/*SPECS*/ } /*SYNTAX*/

/*SPECS*/ void spec__used() {
/*SPECS*/     any(time_t, time); any(size_t, index);

/*SPECS*/     bool res = index_pool_used(pool, time, index);

/*SPECS*/     assert_unchanged();

/*SPECS*/     if (index < pool->size && pool->timestamps[index] != TIME_MAX &&
/*SPECS*/         pool_young(time, pool->expiration_time, index, pool->timestamps[index])) {
/*SPECS*/         assert(res);
/*SPECS*/     } else {
/*SPECS*/         assert(!res);
/*SPECS*/     } /*SYNTAX*/
/*SPECS*/ } /*SYNTAX*/

/*SPECS*/ void spec__return() {
/*SPECS*/     any(size_t, index);
/*SPECS*/     assume(index < pool->size);

/*SPECS*/     index_pool_return(pool, index);

/*SPECS*/     assert(pool->timestamps[index] == TIME_MAX);
/*SPECS*/     assert_unchanged_except_(pool->timestamps[index]);
/*SPECS*/ } /*SYNTAX*/

/*SPECS*/ bool elem_max(size_t *unused, int64_t i) {
/*SPECS*/     if (i < 0 || i >= POOL_SIZE) return true;
/*SPECS*/     return pool->timestamps[i] == TIME_MAX;
/*SPECS*/ } /*SYNTAX*/
/*SPECS*/ void spec__alloc() {
/*SPECS*/     any(time_t, expiration_time);
/*SPECS*/     pool = index_pool_alloc(POOL_SIZE, expiration_time);
/*SPECS*/     assert(forall_elem_(pool->timestamps, &elem_max));
/*SPECS*/ } /*SYNTAX*/