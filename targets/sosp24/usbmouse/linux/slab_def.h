#ifndef _LINUX_SLAB_DEF_H
#define _LINUX_SLAB_DEF_H

#include "../equals.h"
#include <linux/gfp.h>
#include <linux/stddef.h>

//@ predicate kmalloc_block(void *ptr; int size);


void kfree(void *ptr);
/*INTERNAL*/ 	/*@ requires
//INTERNAL// 		ptr == 0 ?
//INTERNAL// 			true
//INTERNAL// 		://SYNTAX//
//INTERNAL// 			kmalloc_block(ptr, ?size)
//INTERNAL// 			&*& uchars_(ptr,size,?cs)
//INTERNAL// 		;//SYNTAX//
//INTERNAL// 	@*///SYNTAX//
//INTERNAL// 	//@ ensures true;


void *kzalloc(size_t size, gfp_t flags);
//INTERNAL// 	/*@ requires size >= 0
//INTERNAL// 		&*& flags != GFP_ATOMIC ?
//INTERNAL// 			not_in_interrupt_context(currentThread)
//INTERNAL// 		:
//INTERNAL// 			true
//INTERNAL// 		;
//INTERNAL// 	@*/
/*INTERNAL*/ 	/*@ ensures
//INTERNAL// 		(result == 0 ? // failure
//INTERNAL// 			true
//INTERNAL// 		: // success
//INTERNAL// 			kmalloc_block(result, size)
//INTERNAL// 			&*& uchars(result, size, ?chars)
			
			// Note: Both forall and forall_pred (a predicate doing the same) are nice for proving that something
			// is all-zero, but hard to conclude something once you have
			// forall or forall_pred.
			&*& forall(chars, (equals)(unit, 0)) == true
		) &*& flags != GFP_ATOMIC ?
			not_in_interrupt_context(currentThread)
		:
			true
		;
	@*/

void *kmalloc(size_t size, gfp_t flags);
	/*@ requires size >= 0
		&*& flags != GFP_ATOMIC ?
			not_in_interrupt_context(currentThread)
		:
			true
		;
	@*/
	/*@ ensures
		(result == 0 ? // failure
			true
		: // success
			kmalloc_block(result, size)
			&*& uchars(result, size, ?chars)
		) &*& flags != GFP_ATOMIC ?
			not_in_interrupt_context(currentThread)
		:
			true
		;
		
	@*/

/*@
// Provide prove that you can't have a malloc_block
// twice for the same address as long as the allocated size
// is not zero.
lemma void *kmalloc_block_unique(void *a, int size);
	requires
		kmalloc_block(a, size) &*& kmalloc_block(a, size)
		&*& size != 0; // kmallocing 0 bytes twice can return successfully with same pointer.
	ensures false;
@*/

#endif
