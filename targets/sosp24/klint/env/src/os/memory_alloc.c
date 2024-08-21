#include "arch/halt.h"
#include "os/log.h"
#include "os/memory.h"

//@ #include "proof/listexex.gh"
//@ #include "proof/modulo.gh"

extern char* memory; // VeriFast behaves oddly if this is an uint8_t*...
extern size_t memory_used_len;

/*@
predicate globals_invariant() =
	memory |-> ?mem &*&
	mem != NULL &*&
	memory_used_len |-> ?memlen &*&
	mem + OS_MEMORY_SIZE <= (void*) UINTPTR_MAX &*&
	mem[memlen..OS_MEMORY_SIZE] |-> ?mem_bytes &*&
	true == all_eq(mem_bytes, 0);

lemma void produce_memory_assumptions(void)
requires emp;
ensures globals_invariant();
{
	// This lemma represents assumptions about the bootloader, compiler, and linker's behavior, which are outside of the scope of VeriFast.
	// Specifically, the preallocated block of memory for the allocator must be well-formed and zeroed.
	assume(false);
}

lemma void consume_memory_assumptions(void)
requires globals_invariant();
ensures emp;
{
	leak globals_invariant();
}
@*/

void* os_memory_alloc(size_t count, size_t size)
//@ requires count * size <= SIZE_MAX;
/*@ ensures chars(result, count * size, ?cs) &*& true == all_eq(cs, 0) &*& result + count * size <= (char*) UINTPTR_MAX &*&
	    result != NULL &*& (size_t) result % (size + CACHE_LINE_SIZE - (size % CACHE_LINE_SIZE)) == 0; @*/
//@ terminates;
{
	//@ mul_nonnegative(count, size);
	const size_t full_size = size * count;

	//@ produce_memory_assumptions();
	//@ open globals_invariant();
	//@ assert memory |-> ?mem;
	//@ assert memory_used_len |-> ?memlen;
	//@ assert mem[memlen..OS_MEMORY_SIZE] |-> ?mem_bytes;
	char* target_addr = memory + memory_used_len;

	// Aligning to the cache line size can make a huge positive performance difference sometimes, well worth the hassle
	// (e.g. one time TinyNF accidentally regressed by 40% throughput because of misalignment...)
	if (SIZE_MAX - CACHE_LINE_SIZE < size) {
		os_debug("Object is too big to be alignable");
		halt();
	}

	//@ div_rem_nonneg(size, CACHE_LINE_SIZE);
	const size_t align_div = size + CACHE_LINE_SIZE - (size % CACHE_LINE_SIZE);
	const size_t align_diff = (size_t) target_addr % align_div;

	//@ div_rem_nonneg((size_t) target_addr, align_div);
	const size_t align_padding = align_diff == 0 ? (size_t) 0 : align_div - align_diff; // VeriFast requires the cast on 0
	if (align_padding > OS_MEMORY_SIZE - memory_used_len) {
		os_debug("Not enough memory left to align");
		halt();
	}

	// Leak the alignment memory, i.e., fragment the heap, since we don't support any notion of freeing
	//@ leak chars((char*)target_addr, align_padding, _);
	//@ all_eq_drop(mem_bytes, align_padding, 0);

	//@ mod_compensate((size_t) target_addr, align_div);
	char* aligned_addr = target_addr + align_padding;

	memory_used_len = memory_used_len + align_padding;
	if (full_size > OS_MEMORY_SIZE - memory_used_len) {
		os_debug("Not enough memory left to allocate");
		halt();
	}

	//@ chars_split((char*) memory + memlen + align_padding, full_size);
	//@ chars_split(aligned_addr, full_size);
	//@ all_eq_take(drop(align_padding, mem_bytes), full_size, 0);
	//@ all_eq_drop(drop(align_padding, mem_bytes), full_size, 0);
	memory_used_len = memory_used_len + full_size;

	return aligned_addr;
	//@ close globals_invariant();
	//@ consume_memory_assumptions();
}
