#ifndef _LINUX_TYPES_H
#define _LINUX_TYPES_H

// TPot: Clang defines this as an unsigned long and won't compile if we redefine it as something else.
// Linux defines this as an unsigned long as well: https://fossd.anu.edu.au/linux/v5.2/source/include/uapi/asm-generic/posix_types.h#L68
// Unsure why the VeriFast case study chose to redefine it.
// typedef unsigned int    __kernel_size_t; // We verify for x86-32.
typedef unsigned long    __kernel_size_t; // We verify for x86-32.

typedef __kernel_size_t         size_t;

#define __bitwise__ 

typedef int dma_addr_t;


// Note: architecture-dependent.
typedef unsigned char __u8;
typedef short __le16; // XXX yes? short?
typedef short __u16;

#endif