#include "verif/drivers.h"

#include "os/memory.h"

#include <stdbool.h>

uint64_t* descriptor_ring_alloc(size_t count) { return os_memory_alloc(count, 2 * sizeof(uint64_t)); }

void* agents_alloc(size_t count, size_t size) { return os_memory_alloc(count, size); }

void foreach_index_forever(size_t length, foreach_index_forever_function* func, void* state)
{
	while (true) {
		for (size_t index = 0; index < length; index++) {
			func(index, state);
		}
	}
}
