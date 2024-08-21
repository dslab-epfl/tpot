#include <tpot_primitives.h>

#include "memory.h"

#include "include/page-def.h"
#include "include/stddef.h"
#include "include/kvm_pgtable.h"

#define NUM_PAGES 1024

extern unsigned long long hyp_physvirt_offset;
extern struct kvm_pgtable_mm_ops hyp_early_alloc_mm_ops;

extern unsigned long base;
extern unsigned long end;
extern unsigned long cur;

void * hyp_early_alloc_page(void *arg);
void * hyp_early_alloc_contig(unsigned int nr_pages);
void hyp_early_alloc_init(unsigned long virt, unsigned long size);