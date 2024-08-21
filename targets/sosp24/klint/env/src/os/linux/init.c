#include "os/init.h"

#include "arch/tsc.h"
#include "os/log.h"
#include "os/memory.h"
#include "os/pci.h"

#include <assert.h>
#include <fcntl.h>
#include <stdlib.h>
#include <sys/io.h>
#include <sys/mman.h>
#include <unistd.h>

// 1 GB hugepages
#define HUGEPAGE_SIZE_POWER (10 + 10 + 10)
#define HUGEPAGE_SIZE (1u << HUGEPAGE_SIZE_POWER)

// The version of musl shipped on Ubuntu 18.04 doesn't define this
#ifndef MAP_HUGE_SHIFT
#define MAP_HUGE_SHIFT 26
#endif

// For clock.h
uint64_t cpu_freq_numerator;
uint64_t cpu_freq_denominator;

// For the shared memory_alloc.c
char* memory;
size_t memory_used_len;

static uint64_t linux_msr_read(uint64_t index)
{
	int msr_fd = open("/dev/cpu/0/msr", O_RDONLY);
	if (msr_fd == -1) {
		os_debug("Could not open MSR file; are you root? did you modprobe msr?");
		abort();
	}

	off_t seek_result = lseek(msr_fd, (off_t) index, SEEK_SET);
	if (seek_result == (off_t) -1) {
		os_debug("Could not seek into MSR file");
		abort();
	}

	uint64_t msr = 0;
	long read_result = read(msr_fd, (void*) &msr, sizeof(msr));
	if (read_result != sizeof(msr)) {
		os_debug("Could not read MSR file");
		abort();
	}

	return msr;
}

void os_init(void)
{
	// First, call ioperm to make sure future PCI accesses will work
	// We access port 0x80 to wait after an outl, since it's the POST port so safe to do anything with (it's what glibc uses in the _p versions of outl/inl)
	// Also note that since reading an int32 is 4 bytes, we need to access 4 consecutive ports for PCI config/data.
	if (ioperm(0x80, 1, 1) < 0 || ioperm(PCI_CONFIG_ADDR, 4, 1) < 0 || ioperm(PCI_CONFIG_DATA, 4, 1) < 0) {
		os_debug("PCI ioperms failed");
		abort();
	}

	// Second, fetch the CPU frequency
	tsc_get_nhz(linux_msr_read, &cpu_freq_numerator, &cpu_freq_denominator);

	// Finally, initialize the memory for the allocator
	// The only way to have pinned pages on Linux is to use huge pages: https://www.kernel.org/doc/Documentation/vm/hugetlbpage.txt
	// Note that Linux's `mlock` system call is not sufficient to pin; it only guarantees the pages will not be swapped out, not that the physical address won't change.
	// While Linux doesn't actually guarantee that huge pages are pinned, in practice its implementation pins them.
	// We use a single 1 GB page to serve everything, which is enough for the allocator
	static_assert(HUGEPAGE_SIZE >= OS_MEMORY_SIZE);
	memory = mmap(
	    // No specific address
	    NULL,
	    // Size of the mapping
	    HUGEPAGE_SIZE,
	    // R/W page
	    PROT_READ | PROT_WRITE,
	    // Hugepage, not backed by a file (and thus zero-initialized); note that without MAP_SHARED the call fails
	    // MAP_POPULATE means the page table will be populated already (without the need for a page fault later),
	    // which is required if the calling code tries to get the physical address of the page without accessing it first.
	    MAP_HUGETLB | (HUGEPAGE_SIZE_POWER << MAP_HUGE_SHIFT) | MAP_ANONYMOUS | MAP_SHARED | MAP_POPULATE,
	    // Required on MAP_ANONYMOUS
	    -1,
	    // Required on MAP_ANONYMOUS
	    0);
	if (memory == MAP_FAILED) {
		os_debug("Allocate mmap failed");
		abort();
	}
	memory_used_len = 0;
}
