#include "os/clock.h"

#include <rte_cycles.h>

void os_clock_sleep_ns(uint64_t ns) { rte_delay_us(ns * 1000); }
