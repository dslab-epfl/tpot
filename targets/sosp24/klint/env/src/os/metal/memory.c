#include "os/memory.h"

void* os_memory_phys_to_virt(uintptr_t addr, size_t size)
{
	// phys == virt, no protections
	(void) size;
	return (void*) addr;
}

uintptr_t os_memory_virt_to_phys(const void* addr)
{
	// phys == virt
	return (uintptr_t) addr;
}
