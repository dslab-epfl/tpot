#include "os/memory.h"       /* LINUX_MODELS */ /*SYNTAX*/
#include <tpot_primitives.h> /* LINUX_MODELS */ /*SYNTAX*/
#include <tpot_annotations.h>/* LINUX_MODELS */ /*SYNTAX*/

/* LOOPINV*/ bool range_zero(char *unused, int64_t j, char *to, int i) {/*SYNTAX*/
/* LOOPINV*/ 	if (j < 0 || j >= i) 
/* LOOPINV*/ 		return true;
/* LOOPINV*/ 	return ((char *) to)[j] == 0;
/* LOOPINV*/ } /*SYNTAX*/
/* LOOPINV*/ bool loopinv_clear(int *i_ptr, size_t **size_ptr, void **to_ptr) {/*SYNTAX*/
/* LOOPINV*/ 	int i = *i_ptr; size_t size = *size_ptr; void *to = *to_ptr;
/* LOOPINV*/ 	return i >= 0 && i < size && forall_elem_((char *)to, &range_zero, (char *)to, i);
/* LOOPINV*/ } /*SYNTAX*/

void *os_memory_alloc(size_t count, size_t size) { /* LINUX_MODELS */
  char *buf = tpot_malloc(count * size);                /* LINUX_MODELS */
  size_t total = count * size;                           /* LINUX_MODELS */
  for (int i = 0; i < count * size; i++) {                  /* LINUX_MODELS */
    _tpot_inv(&loopinv_clear, &i, &total, &buf,             /* LINUX_MODELS */
              // modified memory
              &i, sizeof(i), buf, total);               /* LINUX_MODELS */
    buf[i] = 0;                                         /* LINUX_MODELS */
  }                                                     /* LINUX_MODELS */
} /* LINUX_MODELS */