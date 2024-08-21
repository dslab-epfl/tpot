#include "os/memory.h"

#include "os/log.h"

#include <fcntl.h>
#include <stdbool.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>

static size_t os_memory_pagesize(void)
{
	// sysconf is documented to return -1 on error; let's check all negative cases along the way, to make sure the conversion to unsigned is sound
	const long page_size_long = sysconf(_SC_PAGESIZE);
	if (page_size_long < 0) {
		os_debug("Page size is negative?!?");
		abort();
	}
	if ((unsigned long) page_size_long > SIZE_MAX) {
		os_debug("Page size too big for size_t");
		abort();
	}
	if (page_size_long == 0) {
		os_debug("Could not get page size");
		abort();
	}
	return page_size_long;
}

void* os_memory_phys_to_virt(const uintptr_t addr, const size_t size)
{
	if (addr != (uintptr_t) (off_t) addr) {
		os_debug("Cannot phys-to-virt an addr that does not roundtrip to off_t");
		abort();
	}

	int mem_fd = open("/dev/mem", O_SYNC | O_RDWR);
	if (mem_fd == -1) {
		os_debug("Could not open /dev/mem");
		abort();
	}

	void* mapped = mmap(
	    // No specific address
	    NULL,
	    // Size of the mapping
	    size,
	    // R/W page
	    PROT_READ | PROT_WRITE,
	    // Send updates to the underlying "file"
	    MAP_SHARED,
	    // /dev/mem
	    mem_fd,
	    // Offset is the address (cast OK because we checked above)
	    (off_t) addr);

	// nothing we can do if this fails, since we didn't write don't even bother checking
	close(mem_fd);

	if (mapped == MAP_FAILED) {
		os_debug("Phys-to-virt mmap failed");
		abort();
	}

	return mapped;
}

// See https://www.kernel.org/doc/Documentation/vm/pagemap.txt
uintptr_t os_memory_virt_to_phys(const void* const addr)
{
	const size_t page_size = os_memory_pagesize();
	const uintptr_t page = (uintptr_t) addr / page_size;
	const uintptr_t map_offset = page * sizeof(uint64_t);
	if (map_offset != (uintptr_t) (off_t) map_offset) {
		os_debug("Cannot virt-to-phys with an offset that does not roundtrip to off_t");
		abort();
	}

	const int map_fd = open("/proc/self/pagemap", O_RDONLY);
	if (map_fd < 0) {
		os_debug("Could not open the pagemap");
		abort();
	}

	if (lseek(map_fd, (off_t) map_offset, SEEK_SET) == (off_t) -1) {
		os_debug("Could not seek the pagemap");
		abort();
	}

	uint64_t metadata;
	const ssize_t read_result = read(map_fd, &metadata, sizeof(uint64_t));
	close(map_fd);
	if (read_result != sizeof(uint64_t)) {
		os_debug("Could not read the pagemap");
		abort();
	}

	// We want the PFN, but it's only meaningful if the page is present; bit 63 indicates whether it is
	if ((metadata & 0x8000000000000000) == 0) {
		os_debug("Page not present");
		abort();
	}
	// PFN = bits 0-54
	const uint64_t pfn = metadata & 0x7FFFFFFFFFFFFF;
	if (pfn == 0) {
		os_debug("Page not mapped");
		abort();
	}

	const uintptr_t addr_offset = (uintptr_t) addr % page_size;
	return pfn * page_size + addr_offset;
}
