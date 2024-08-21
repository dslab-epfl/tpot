#pragma once

#include "arch/tsc.h"
#include "os/time.h"

#include <stdint.h>

// Fetched at startup by the OS, to make the time call as fast as possible, it's on the critical path
extern uint64_t cpu_freq_numerator;
extern uint64_t cpu_freq_denominator;

// Gets the current time in nanoseconds, according to a monotonic clock with an undefined starting point.
// It's a safe assumption that this never returns TIME_MAX, allowing containers that store a time to optimize storage; anyway, reaching the end of time would be problematic
static inline time_t os_clock_time_ns(void) { return tsc_get() / cpu_freq_numerator * cpu_freq_denominator; }

// Sleeps for at least the given amount of nanoseconds.
// TODO This function would not be necessary if symbex could handle loops;
//      it could be implemented inline as a busy-waiting loop with a "pause" hint
void os_clock_sleep_ns(uint64_t ns);
//@ requires emp;
//@ ensures emp;
