#include "os/clock.h"

void os_clock_sleep_ns(uint64_t ns)
{
	time_t target = os_clock_time_ns() + ns;
	while (os_clock_time_ns() != target) {
		// Nothing (TODO: CPU pause?)
	}
}
