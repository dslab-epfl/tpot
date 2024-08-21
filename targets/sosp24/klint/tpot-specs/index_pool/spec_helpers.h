
#include <tpot_primitives.h>
#include "structs/index_pool.h"

// copied from index_pool.c
struct index_pool {
	time_t* timestamps;
	size_t size;
	time_t expiration_time;
	size_t last_borrowed_index;
};

extern struct index_pool *pool;

// --- helpers --- //
/*SPECS*/ bool pool_young(time_t time, time_t expiration_time, size_t k, time_t v) {
/*SPECS*/     return time < expiration_time || time - expiration_time <= v;
/*SPECS*/ } /*SYNTAX*/