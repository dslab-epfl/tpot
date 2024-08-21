// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright (C) 2020 Google, inc
 * Author: Quentin Perret <qperret@google.com>
 */

/* CP: originally at linux/arch/arm64/kvm/hyp/nvhe/early_alloc.c */


/* CP: originally: #include <asm/kvm_pgtable.h> */

/* CP: originally: #include <nvhe/memory.h> */
#include "memory.h"

/* CP: adding */
#include "include/page-def.h"
#include "include/stddef.h"
#include "include/kvm_pgtable.h"
#include "verifast_predicates.h"

/* CP: originally: s64 hyp_physvirt_offset; */
unsigned long long hyp_physvirt_offset;
struct kvm_pgtable_mm_ops hyp_early_alloc_mm_ops;

static unsigned long base;
static unsigned long end;
static unsigned long cur;

unsigned long hyp_early_alloc_nr_pages(void)
//@ requires base |-> ?base_val &*& cur |-> ?cur_val &*& base_val <= cur_val;                          /*SPECS*/ 
//@ ensures base|-> base_val &*& cur |-> cur_val &*& result == (cur_val-base_val) >> PAGE_SHIFT;       /*SPECS*/ 
{
	return (cur - base) >> PAGE_SHIFT;
}

/* CP: originally: extern void clear_page(void *to); */
/* CP: instead, making up a definition of this */
void clear_page(void *to) 
//@ requires chars(to, 4096, _);                                                     /*INTERNAL*/ 
//@ ensures characters_zeroed(to, 4096);                                             /*INTERNAL*/ 
{
  int i = 0;
  while(i < 4096) 
  //@ requires chars(to + i, PAGE_SIZE - i, _);                                      /*LOOPINV*/
  //@ ensures  characters_zeroed((char*) to + old_i, PAGE_SIZE - old_i);             /*LOOPINV*/
  {
    ((char *) to)[i] = 0;
    i++;
  };
}

void * hyp_early_alloc_page(void *arg)
/*@ requires cur |-> ?cur_val &*& end |-> ?end_val &*&                               /*SPECS*/ 
             cur_val + 4096 <= end_val && end_val <= UINTPTR_MAX &*&                 /*SPECS*/ 
             earlyAlloc((char*) cur_val, end_val); @*/                               /*SPECS*/ 
/*@ ensures cur |-> ?cur_val' &*& end |-> end_val &*&                                /*SPECS*/ 
            earlyAlloc((char*) cur_val', end_val) &*&                                /*SPECS*/ 
            characters_zeroed((char*)result, PAGE_SIZE) &*&                          /*SPECS*/ 
            cur_val' == cur_val + PAGE_SIZE; @*/                                     /*SPECS*/ 
{
        /*PREDICATES*/ /*VERIFAST*/ //@ open earlyAlloc((char*) cur, end);
	unsigned long ret = cur;

	cur += PAGE_SIZE;
	if (cur > end) {
		cur = ret;
		return NULL;
	}
	clear_page((void*)ret);

        /*PREDICATES*/ /*VERIFAST*/ //@ close earlyAlloc((char*) cur, end);
	return (void *)ret;
}

#include "lemmas.h"

/* CP: We also include this variant of hyp_early_alloc_page that
   allocates a number of pages, as found in newer versions of
   early_alloc.c */
void *hyp_early_alloc_contig(unsigned int nr_pages)
/*@ requires cur |-> ?cur_val &*& end |-> ?end_val &*&                               /*SPECS*/ 
             nr_pages > 0 &*& (nr_pages * 4096) < UINT_MAX &*&                       /*SPECS*/ 
             cur_val + 4096*nr_pages <= end_val && end_val <= UINTPTR_MAX &*&        /*SPECS*/ 
             earlyAlloc((char*) cur_val, end_val); @*/                               /*SPECS*/ 
/*@ ensures cur |-> ?cur_val' &*& end |-> end_val &*&                                /*SPECS*/ 
            earlyAlloc((char*) cur_val', end_val) &*&                                /*SPECS*/ 
            characters_zeroed((char*)result, PAGE_SIZE*nr_pages) &*&                 /*SPECS*/ 
            cur_val' == cur_val + PAGE_SIZE*nr_pages; @*/                            /*SPECS*/ 
{
        /*PREDICATES*/ /*VERIFAST*/ //@ open earlyAlloc((char*) cur, end);
	unsigned long ret = cur, i, p;

	if (!nr_pages)
		return NULL;

	cur += nr_pages << PAGE_SHIFT;
	if (cur > end) {
		cur = ret;
		return NULL;
	}

	for (i = 0; i < nr_pages; i++) 
        /*@ invariant cur |-> ?cur_val'' &*& end |-> end_val &*&                     /*LOOPINV*/
          cur_val'' == cur_val + (nr_pages * 4096) &*&                               /*LOOPINV*/
          ret == cur_val &*& (0 <= i && i <= nr_pages) &*&                           /*LOOPINV*/
          characters_zeroed((char*) ret, i*4096) &*&                                 /*LOOPINV*/
          chars((char*) cur_val + i*4096, (end_val - cur_val - i*4096), _) ;@*/      /*LOOPINV*/
        {
		p = ret + (i << PAGE_SHIFT);
		clear_page((void *)(p));
	}

        /*PREDICATES*/ /*VERIFAST*/ //@ close earlyAlloc((char*) cur, end);
	return (void *)ret;
}


void hyp_early_alloc_init(unsigned long virt, unsigned long size)
/*@ requires base |-> _ &*& cur |-> _ &*& end |-> _ &*& kvm_pgtable_mm_ops(&hyp_early_alloc_mm_ops) &*&                   /*SPECS*/ 
             virt + size <= ULONG_MAX &*& chars((char*) virt, size, _); @*/                                               /*SPECS*/ 
/*@ ensures base |-> virt &*& end |-> virt + size &*& cur |-> virt &*& kvm_pgtable_mm_ops(&hyp_early_alloc_mm_ops) &*&    /*SPECS*/ 
            earlyAlloc((char*) virt, virt+size); @*/                                                                      /*SPECS*/ 
{
	base = virt;
	end = virt + size;
	cur = virt;

	hyp_early_alloc_mm_ops.zalloc_page = hyp_early_alloc_page;
	hyp_early_alloc_mm_ops.phys_to_virt = hyp_phys_to_virt;
	hyp_early_alloc_mm_ops.virt_to_phys = hyp_virt_to_phys;
	
	/*PREDICATES*/ /*VERIFAST*/ //@ close earlyAlloc((char*) cur, end);
}
