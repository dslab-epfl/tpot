#include "os/init.h"

#include "arch/msr.h"
#include "arch/tsc.h"
#include "os/memory.h"

// For clock.h
uint64_t cpu_freq_numerator;
uint64_t cpu_freq_denominator;

// For the shared memory allocator
char memory[OS_MEMORY_SIZE]; // zero-initialized
size_t memory_used_len;

void os_init(void) { tsc_get_nhz(msr_read, &cpu_freq_numerator, &cpu_freq_denominator); }
