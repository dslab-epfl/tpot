#include <stdbool.h>
#include <stdarg.h>
#include <tpot_primitives.h>  // for tpot_assume, tpot_assert, tpot_malloc, tpot_free

extern void __tpot_inv(void *cond, ...);
#define _tpot_inv(cond, ...) __tpot_inv(cond, __VA_ARGS__);

extern void tpot_memset(void *dst, uint64_t val, size_t s);
extern void tpot_memcpy(void *src, void *dst, size_t s);

// -- Overrides -- //
#define assert(cond) tpot_assert(cond)
#define assume(cond) tpot_assume(cond)
#define malloc(ptr) tpot_malloc(ptr)
#define free(ptr)  tpot_free(ptr)
#define memcpy(dest, src, n) tpot_memcpy(dest, src, n)
#define memset(dest, val, n) tpot_memset(dest, val, n)
