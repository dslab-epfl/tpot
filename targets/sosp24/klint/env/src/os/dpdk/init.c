#include "os/init.h"

#include <rte_cycles.h>
#include <rte_debug.h>

// For clock.h
uint64_t cpu_freq_numerator;
uint64_t cpu_freq_denominator;

void os_init(void)
{
	cpu_freq_numerator = rte_get_tsc_hz();
	if (cpu_freq_numerator == 0) {
		rte_panic("Could not get TSC freq");
	}
	cpu_freq_denominator = 1000000000ull;
	while (cpu_freq_numerator % 10 == 0) {
		cpu_freq_numerator = cpu_freq_numerator / 10;
		cpu_freq_denominator = cpu_freq_denominator / 10;
	}
}
