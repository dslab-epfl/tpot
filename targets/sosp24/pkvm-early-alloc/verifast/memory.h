// SPDX-License-Identifier: GPL-2.0-only
/* CP: originally at linux/arch/arm64/kvm/hyp/include/nvhe/memory.h */
#ifndef __KVM_HYP_MEMORY_H
#define __KVM_HYP_MEMORY_H

/* CP: originally #include <asm/page.h> */

/* CP: originally #include <linux/types.h> */

/* CP: adding */ 
#include "include/kernel.h"

/* CP: originally: extern s64 hyp_physvirt_offset; */
/* CP: commenting this out, so VeriFast does not reject it due to
   duplicate global definitions */

#define __hyp_pa(virt)	((phys_addr_t)(virt) + hyp_physvirt_offset)
#define __hyp_va(virt)	(void*)((phys_addr_t)(virt) - hyp_physvirt_offset)

static inline void *hyp_phys_to_virt(phys_addr_t phys)
/*@ requires hyp_physvirt_offset |-> ?offset &*&                                          /*INTERNAL*/
             0 <= offset && 0 <= phys - offset && phys - offset < UINTPTR_MAX; @*/        /*INTERNAL*/
/*@ ensures hyp_physvirt_offset |-> offset &*&                                            /*INTERNAL*/
	    result == (void*) (phys - offset); @*/                                        /*INTERNAL*/
{
	return __hyp_va(phys);
}

static inline phys_addr_t hyp_virt_to_phys(void* addr)
/*@ requires hyp_physvirt_offset |-> ?offset &*&                                                                    /*INTERNAL*/
             0 <= offset && 0 <= (phys_addr_t)addr + offset && (phys_addr_t) addr + offset < UINTPTR_MAX; @*/       /*INTERNAL*/
/*@ ensures hyp_physvirt_offset |-> offset &*&                                                                      /*INTERNAL*/
            result == (phys_addr_t)addr + offset; @*/                                                               /*INTERNAL*/
{
	return __hyp_pa(addr);
}

#endif /* __KVM_HYP_MEMORY_H */
