#include "spec_helpers.h"

bool inv__early_alloc() { // GLOBAL /*SYNTAX*/
    return names_obj((char *)base, char[NUM_PAGES * PAGE_SIZE]) && // GLOBAL
           end == base + NUM_PAGES * PAGE_SIZE && // GLOBAL
           cur >= base && cur <= end; // GLOBAL
} // GLOBAL  /*SYNTAX*/

/*SPECS*/ /*SYNTAX*/ void spec__nr_pages() {
/*SPECS*/     unsigned long result = hyp_early_alloc_nr_pages();
/*SPECS*/     assert(result == (cur - base) / PAGE_SIZE);
/*SPECS*/ }  /*SYNTAX*/

/*SPECS*/ /*SYNTAX*/ bool alloc_range_zero(int *unused, int64_t i, int64_t start, int64_t end) {
/*SPECS*/    if (i < start || i >= end) return true;
/*SPECS*/    return ((char *)base)[i] == 0;
/*SPECS*/}  /*SYNTAX*/

/*SPECS*/ /*SYNTAX*/ void spec__alloc_page() {
/*SPECS*/     assume(cur + PAGE_SIZE < end);

/*SPECS*/     unsigned long prev_end = end, prev_cur = cur;

/*SPECS*/     char *result = hyp_early_alloc_page(0);

/*SPECS*/     assert(result != NULL);
/*SPECS*/     assert(forall_elem_((char *)base, &alloc_range_zero, prev_cur - base, prev_cur - base + PAGE_SIZE));

/*SPECS*/     assert(cur == prev_cur + PAGE_SIZE);
/*SPECS*/     assert(end == prev_end);
/*SPECS*/ }  /*SYNTAX*/

/*SPECS*/ /*SYNTAX*/ void spec__alloc_contig() {
/*SPECS*/     any(unsigned int, nr_pages);
/*SPECS*/     assume(nr_pages > 0);
/*SPECS*/     assume(cur + PAGE_SIZE  * nr_pages < end);

/*SPECS*/     unsigned long prev_end = end, prev_cur = cur;

/*SPECS*/     char *result = hyp_early_alloc_contig(nr_pages);

/*SPECS*/     assert(result != NULL);
/*SPECS*/     assert(forall_elem_((char *)base, &alloc_range_zero, 
/*SPECS*/            prev_cur - base, prev_cur - base + PAGE_SIZE * nr_pages));

/*SPECS*/     assert(cur == prev_cur + PAGE_SIZE * nr_pages);
/*SPECS*/     assert(end == prev_end);
/*SPECS*/ }  /*SYNTAX*/

/*SPECS*/ /*SYNTAX*/ void spec__init() {
/*SPECS*/     any(unsigned long, virt);
/*SPECS*/     assume(names_obj((char *)virt, char[NUM_PAGES * PAGE_SIZE]));

/*SPECS*/     hyp_early_alloc_init(virt, NUM_PAGES * PAGE_SIZE);
/*SPECS*/ }  /*SYNTAX*/