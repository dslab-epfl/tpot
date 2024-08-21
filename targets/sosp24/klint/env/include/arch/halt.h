#pragma once

#ifndef VERIFAST

_Noreturn static inline void halt(void)
{
	__asm__ volatile("hlt");
	__builtin_unreachable(); // otherwise the compiler complains, because it doesn't know hlt semantics
}

#else
// TODO VeriFast should know about __builtin_unreachable; how to properly model __asm__ though? (probably in a very conservative "any asm could do anything" way)
#include <stdlib.h>
_Noreturn static inline void halt(void)
//@ requires emp;
//@ ensures false;
//@ terminates;
{
	exit(0);
}
#endif
