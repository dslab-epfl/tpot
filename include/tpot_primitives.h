#ifndef TPOT_PRIMITIVES_H
#define TPOT_PRIMITIVES_H

#include <klee.h>
#include <stdarg.h> // for va_list
#include <stdbool.h>
#include <stdint.h> 

// -- Functions with special interpretations -- // 
extern int      __tpot_assert(bool cond);
extern void     __tpot_assume(void *lambda, ...);
extern void *   __tpot_fresh_bv(char *name, int width, ...);
extern bool     __tpot_points_to(void *ptr, const char *name, size_t size);
extern bool     __tpot_forall_elem(void *arr, size_t arr_sz, size_t elem_sz, void *elem_zero_addr, void *field_addr, void *cond, ...);
extern bool     __tpot_names_obj_forall(void *ptr, void *sz, const char *name);
extern bool     __tpot_names_obj_forall_cond(void *ptr, void *sz, const char *name, void *cond);
extern void     __tpot_switch_old();
extern void     __tpot_switch_new();
extern void     __tpot_uninterpreted(void *func);
extern void     __tpot_free(void *ptr);
// ! These are for debugging TPot, and should not be used in the final code.
extern void     __tpot_skip_invariant_check();
extern void     __tpot_debug_print(const char *string);

extern void *__tpot_malloc(size_t size);
// -- Core API -- //
#define tpot_assume(cond) klee_assume(cond)
#define tpot_assert(cond) __tpot_assert(cond)
#define any(type, i) \
    type i = __tpot_fresh_bv(#i, sizeof(type) * 8, i);
#define points_to(ptr, name, typ) __tpot_points_to(ptr, name, sizeof(typ))
#define names_obj_forall(ptr, sz)                   \
    __tpot_names_obj_forall(ptr, sz, #ptr)
#define names_obj_forall_cond(ptr, sz, cond)        \
    __tpot_names_obj_forall_cond(ptr, sz, #ptr, cond)
#define forall_elem_(arr, ...) __tpot_forall_elem((arr), sizeof((arr)), sizeof((arr)[0]), &((arr)[0]), &((arr)[0]), __VA_ARGS__)

// -- Helper API -- //
#define names_obj(ptr, typ) points_to(ptr, #ptr, typ)
#define tpot_implies(prem, cons) ~prem | cons
#define assert(cond) tpot_assert(cond)
#define assume(cond) tpot_assume(cond)
#define assert_old(expr) \
    __tpot_switch_old();  \
    assert(expr);        \
    __tpot_switch_new();
#define tpot_uninterpreted(func) __tpot_uninterpreted(&func);
#define tpot_malloc(size) __tpot_malloc(size)
#define tpot_free(ptr) __tpot_free(ptr)
#define _assert_unchanged_except(...) __tpot_assert_unchanged_except(__VA_ARGS__)
#define assert_unchanged_except_(field) _assert_unchanged_except(&field, sizeof(field))
#define assert_unchanged_except__(f1, f2) _assert_unchanged_except(&f1, sizeof(f1), &f2, sizeof(f2))
#define assert_unchanged() _assert_unchanged_except();

#endif // TPOT_PRIMITIVES_H