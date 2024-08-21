/*
 * Clang requires that freestanding environment provide smemcpy, memmove, memset and memcmp.
 * (https://groups.google.com/g/llvm-dev/c/TxuxaOqkK6U/m/zJ4illVSwzwJ).
 *
 * Some other C verifiers define special interpretations for these functions. 
 * We instead provide implementations that are verifed by TPot itself.
 */

#include <tpot_annotations.h> // tpot_inv
#include <tpot_primitives.h> // forall_elem_

// ------------------------------ //
//            memset              //
// ------------------------------ //
bool prev_elems_set(uint64_t *unused, int64_t j, int64_t i, uint64_t val, uint64_t *dst) {
    if (j < 0 || j >= i) return true;
    return dst[j] == val;
}

bool loopinv_memset(size_t *i_ptr, uint64_t *val_ptr, uint64_t **dst_ptr, size_t *s_ptr) {
    size_t i = *i_ptr; uint64_t val = *val_ptr; uint64_t *dst = *dst_ptr; size_t s = *s_ptr;
    return i >= 0 && i * sizeof(uint64_t) < s &&
            forall_elem_(dst, &prev_elems_set, i, val, dst);
}
void tpot_memset(void *dst, uint64_t val, size_t s) {
    uint64_t *dst_src = (uint64_t *)dst;

    size_t i = 0;
    while (i * sizeof(uint64_t) < s) {
        _tpot_inv(&loopinv_memset, &i, &val, &dst_src, &s, 
        
        // modified memory
        &i, sizeof(i),
        dst, s
        );

        dst_src[i] = val;
        i = i + 1;
    }
}

// ------------------------------ //
//            memcpy              //
// ------------------------------ //
bool prev_elems_copied(uint64_t *unused, int64_t j, int64_t i, uint64_t *src, uint64_t *dst) {
    if (j < 0 || j >= i) return true;
    return src[j] == dst[j];
}

bool loopinv_memcpy(size_t *i_ptr, uint64_t **src_ptr, uint64_t **dst_ptr, size_t *s_ptr) {
    size_t i = *i_ptr; uint64_t *src = *src_ptr; uint64_t *dst = *dst_ptr; size_t s = *s_ptr;
    return i >= 0 && i * sizeof(uint64_t) < s &&
            forall_elem_(src, &prev_elems_copied, i, src, dst);
}
void tpot_memcpy(void *src, void *dst, size_t s) {
    uint64_t *arr_src = (uint64_t *)src;
    uint64_t *dst_src = (uint64_t *)dst;

    size_t i = 0;
    while (i * sizeof(uint64_t) < s) {
        _tpot_inv(&loopinv_memcpy, &i, &arr_src, &dst_src, &s, 
        
        // modified memory
        &i, sizeof(i),
        dst, s
        );

        dst_src[i] = arr_src[i];
        i = i + 1;
    }
}