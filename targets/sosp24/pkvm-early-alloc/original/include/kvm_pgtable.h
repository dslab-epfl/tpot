// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright (C) 2020 Google LLC
 * Author: Will Deacon <will@kernel.org>
 */
/* CP: originally at linux/arch/arm64/include/asm/kvm_pgtable.h */

/* CP: removing everything except this struct definition, and adding a definition for size_t */
/* CP: also, so we can parse this with VeriFast, organise separate
   typedefs for the struct members */

typedef unsigned long size_t;

typedef void* kvm_pgtable_mm_ops__zalloc_page_t(void *arg);
typedef void* kvm_pgtable_mm_ops__zalloc_pages_exact_t(size_t size);
typedef void kvm_pgtable_mm_ops__free_pages_exact_t(void *addr, size_t size);
typedef void kvm_pgtable_mm_ops__get_page_t(void *addr);
typedef void kvm_pgtable_mm_ops__put_page_t(void *addr);
typedef int kvm_pgtable_mm_ops__page_count(void *addr);
typedef void* kvm_pgtable_mm_ops__phys_to_virt_t(phys_addr_t phys);
typedef phys_addr_t kvm_pgtable_mm_ops__virt_to_phys(void* addr);

struct kvm_pgtable_mm_ops {
	kvm_pgtable_mm_ops__zalloc_page_t		*zalloc_page;
	kvm_pgtable_mm_ops__zalloc_pages_exact_t		*zalloc_pages_exact;
	kvm_pgtable_mm_ops__free_pages_exact_t		*free_pages_exact;
	kvm_pgtable_mm_ops__get_page_t		*get_page;
	kvm_pgtable_mm_ops__put_page_t		*put_page;
	kvm_pgtable_mm_ops__page_count		*page_count;
	kvm_pgtable_mm_ops__phys_to_virt_t		*phys_to_virt;
	kvm_pgtable_mm_ops__virt_to_phys	*virt_to_phys;
};

