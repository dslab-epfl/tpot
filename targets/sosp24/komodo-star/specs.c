#include "specs.h"
#include "monitor.h"
#include "tpot_primitives.h"
#include "uapi/komodo/memregions.h"

struct page_entry *_payload_start;

//helper
static kom_secure_pageno_t get_pgno(struct kom_addrspace *ptr) {
  return (kom_secure_pageno_t)(((uint64_t)ptr - (uint64_t)secure_pages) / PAGE_SIZE);
}

/**
(define (spec-kom_smc_enter s disp_page a0 a1 a2)
  (define addrspace_page ((state-pagedb.addrspace s) disp_page))
  (cond
    [(! (page-typed? s disp_page komodo:KOM_PAGE_DISPATCHER))
      (set-return! s komodo:KOM_ERR_INVALID_PAGENO)]
    [(! (addrspace-state? s addrspace_page komodo:KOM_ADDRSPACE_FINAL))
      (set-return! s komodo:KOM_ERR_NOT_FINAL)]
    [(! (bvzero? (state-dispatcher.entered s disp_page)))
      (set-return! s komodo:KOM_ERR_ALREADY_ENTERED)]
    [else
      (update-state-dispatcher.regs.a0! s disp_page a0)
      (update-state-dispatcher.regs.a1! s disp_page a1)
      (update-state-dispatcher.regs.a2! s disp_page a2)

      (spec-enter_secure_world s disp_page)]))
*/
void spec_kom_smc_enter() {
  any(kom_secure_pageno_t, disp_page);
  any(uintptr_t, a0);
  any(uintptr_t, a1);
  any(uintptr_t, a2);

  if (disp_page < 0) {
    return;
  }

  // [(! (page-typed? s disp_page komodo:KOM_PAGE_DISPATCHER))
  //   (set-return! s komodo:KOM_ERR_INVALID_PAGENO)]
  if (disp_page >= KOM_SECURE_NPAGES || g_pagedb[disp_page].type != KOM_PAGE_DISPATCHER) {
    int result = kom_smc_enter(disp_page, a0, a1, a2);
    assert(result == KOM_ERR_INVALID_PAGENO);
    return;
  }
  assert(disp_page < KOM_SECURE_NPAGES && disp_page >= 0 && g_pagedb[disp_page].type == KOM_PAGE_DISPATCHER);

  // [(! (addrspace-state? s addrspace_page komodo:KOM_ADDRSPACE_FINAL))
  //   (set-return! s komodo:KOM_ERR_NOT_FINAL)]
  // uint64_t addrspace_page = g_pagedb[disp_page].addrspace_page;
  // assert(addrspace_page < KOM_SECURE_NPAGES);
  // struct kom_addrspace *addrspace = (struct kom_addrspace *)&secure_pages[addrspace_page];
  struct kom_addrspace *addrspace = g_pagedb[disp_page].addrspace;
  assert(addrspace != NULL);
  if (addrspace->state != KOM_ADDRSPACE_FINAL) {
    int result = kom_smc_enter(disp_page, a0, a1, a2);
    assert(result == KOM_ERR_NOT_FINAL);
    return;
  }

  // [(! (bvzero? (state-dispatcher.entered s disp_page)))
  //   (set-return! s komodo:KOM_ERR_ALREADY_ENTERED)]
  // (define (state-dispatcher.entered s pageno)
  //   ((state-pages s) pageno (bvpointer komodo:KOM_DISPATCHER_ENTERED)))
  struct kom_dispatcher *dispatcher = (struct kom_dispatcher *)&secure_pages[disp_page];
  if (dispatcher->entered != 0) {
    int result = kom_smc_enter(disp_page, a0, a1, a2);
    assert(result == KOM_ERR_ALREADY_ENTERED);
    return;
  }

  // (update-state-dispatcher.regs.a0! s disp_page a0)
  // (update-state-dispatcher.regs.a1! s disp_page a1)
  // (update-state-dispatcher.regs.a2! s disp_page a2)

  int result = kom_smc_enter(disp_page, a0, a1, a2);
  assert(result == KOM_ERR_SUCCESS);
  assert(dispatcher->regs.a0 == a0);
  assert(dispatcher->regs.a1 == a1);
  assert(dispatcher->regs.a2 == a2);
  return;
}

/**
(define (spec-kom_smc_resume s disp_page)
  (define addrspace_page ((state-pagedb.addrspace s) disp_page))
  (cond
    [(! (page-typed? s disp_page komodo:KOM_PAGE_DISPATCHER))
      (set-return! s komodo:KOM_ERR_INVALID_PAGENO)]
    [(! (addrspace-state? s addrspace_page komodo:KOM_ADDRSPACE_FINAL))
      (set-return! s komodo:KOM_ERR_NOT_FINAL)]
    [(bvzero? (state-dispatcher.entered s disp_page))
      (set-return! s komodo:KOM_ERR_NOT_ENTERED)]
    [else
      (spec-enter_secure_world s disp_page)]))
*/
void spec_kom_smc_resume() {
  any(kom_secure_pageno_t, disp_page);

  if (disp_page < 0) {
    return;
  }

  // [(! (page-typed? s disp_page komodo:KOM_PAGE_DISPATCHER))
  //   (set-return! s komodo:KOM_ERR_INVALID_PAGENO)]
  if (disp_page >= KOM_SECURE_NPAGES || g_pagedb[disp_page].type != KOM_PAGE_DISPATCHER) {
    int result = kom_smc_resume(disp_page);
    assert(result == KOM_ERR_INVALID_PAGENO);
    return;
  }
  assert(disp_page < KOM_SECURE_NPAGES && g_pagedb[disp_page].type == KOM_PAGE_DISPATCHER);

  // [(! (addrspace-state? s addrspace_page komodo:KOM_ADDRSPACE_FINAL))
  //   (set-return! s komodo:KOM_ERR_NOT_FINAL)]
  // uint64_t addrspace_page = g_pagedb[disp_page].addrspace_page;
  // assert(addrspace_page < KOM_SECURE_NPAGES);
  // struct kom_addrspace *addrspace = (struct kom_addrspace *)&secure_pages[addrspace_page];
  struct kom_addrspace *addrspace = g_pagedb[disp_page].addrspace;
  assert(addrspace != NULL);
  if (addrspace->state != KOM_ADDRSPACE_FINAL) {
    int result = kom_smc_resume(disp_page);
    assert(result == KOM_ERR_NOT_FINAL);
    return;
  }

  // [(bvzero? (state-dispatcher.entered s disp_page))
  //   (set-return! s komodo:KOM_ERR_NOT_ENTERED)]
  struct kom_dispatcher *dispatcher = (struct kom_dispatcher *)&secure_pages[disp_page];
  if (dispatcher->entered == 0) {
    int result = kom_smc_resume(disp_page);
    assert(result == KOM_ERR_NOT_ENTERED);
    return;
  }

  int result = kom_smc_resume(disp_page);
  assert(result == KOM_ERR_SUCCESS);
  return;
}

/**
(define (spec-kom_handle_trap s cause)
  (when (state-enclave-mode s)
    (set-state-host-state! s (struct-copy regs (state-host-state s)
      [a0 (if (bvslt cause (bv 0 64))
              (bv komodo:KOM_ERR_INTERRUPTED 64)
              (bv komodo:KOM_ERR_FAULT 64))]
      [a1 cause]))
    (define cur-dispatcher (state-current-dispatcher s))
    (leave_secure_world s cur-dispatcher #t)))
*/
void spec_kom_handle_trap() {
  any(long, cause);

  uintptr_t a0;
  if (cause < 0) {
    a0 = KOM_ERR_INTERRUPTED;
  } else {
    a0 = KOM_ERR_FAULT;
  }
  int result = kom_handle_trap(cause);
  assert(result == KOM_ERR_SUCCESS);
  assert(host_state.regs.a0 == a0);
  assert(host_state.regs.a1 == cause);
}

/**
(define (spec-kom_svc_exit s exitvalue)
  (define newmepc (bvadd (bv 4 64) (regs-mepc (state-regs s))))
  (set-state-regs! s (struct-copy regs (state-regs s) [mepc newmepc]))
  (cond
    [(! (state-enclave-mode s)) (set-return! s (- komodo:ENOSYS))]
    [else
      (set-state-host-state! s (struct-copy regs (state-host-state s)
        [a0 (bv 0 64)]
        [a1 exitvalue]))

      (define cur-dispatcher (state-current-dispatcher s))
      (leave_secure_world s cur-dispatcher #f)

    ]))
*/
void spec_kom_svc_exit() {
  any(long, exitvalue);

  int result = kom_svc_exit(exitvalue);
  assert(result == KOM_ERR_SUCCESS);
  assert(host_state.regs.a0 == 0);
  assert(host_state.regs.a1 == exitvalue);
}

/**
(define (spec-kom_smc_stop s addrspace_page)
  (cond
    [(! (page-typed? s addrspace_page komodo:KOM_PAGE_ADDRSPACE))
      (set-return! s komodo:KOM_ERR_INVALID_ADDRSPACE)]
    [else
      (update-state-addrspace.state! s addrspace_page (bv komodo:KOM_ADDRSPACE_STOPPED 64))

      (set-return! s komodo:KOM_ERR_SUCCESS)]))
*/
void spec_kom_smc_stop() {
  any(kom_secure_pageno_t, addrspace_page);

  if (addrspace_page < 0) {
    return;
  }

  if (addrspace_page >= KOM_SECURE_NPAGES || g_pagedb[addrspace_page].type != KOM_PAGE_ADDRSPACE) {
    int result = kom_smc_stop(addrspace_page);
    assert(result == KOM_ERR_INVALID_ADDRSPACE);
    return;
  }
  assert(addrspace_page < KOM_SECURE_NPAGES && g_pagedb[addrspace_page].type == KOM_PAGE_ADDRSPACE);

  int result = kom_smc_stop(addrspace_page);
  assert(result == KOM_ERR_SUCCESS);
  struct kom_addrspace *address = (struct kom_addrspace *)&secure_pages[addrspace_page];
  assert(address->state == KOM_ADDRSPACE_STOPPED);
}

/**
(define (spec-kom_smc_finalise s addrspace_page)
  (cond
    [(! (page-typed? s addrspace_page komodo:KOM_PAGE_ADDRSPACE))
      (set-return! s komodo:KOM_ERR_INVALID_ADDRSPACE)]
    [(! (addrspace-state? s addrspace_page komodo:KOM_ADDRSPACE_INIT))
      (set-return! s komodo:KOM_ERR_ALREADY_FINAL)]
    [else
      (update-state-addrspace.state! s addrspace_page (bv komodo:KOM_ADDRSPACE_FINAL 64))

      (set-return! s komodo:KOM_ERR_SUCCESS)]))
*/
void spec_kom_smc_finalise() {
  any(kom_secure_pageno_t, addrspace_page);

  if (addrspace_page < 0) {
    return;
  }

  if (addrspace_page >= KOM_SECURE_NPAGES || g_pagedb[addrspace_page].type != KOM_PAGE_ADDRSPACE) {
    int result = kom_smc_finalise(addrspace_page);
    assert(result == KOM_ERR_INVALID_ADDRSPACE);
    return;
  }
  assert(addrspace_page < KOM_SECURE_NPAGES && g_pagedb[addrspace_page].type == KOM_PAGE_ADDRSPACE);

  struct kom_addrspace *address = (struct kom_addrspace *)&secure_pages[addrspace_page];
  if (address->state != KOM_ADDRSPACE_INIT) {
    int result = kom_smc_finalise(addrspace_page);
    assert(result == KOM_ERR_ALREADY_FINAL);
    return;
  }

  int result = kom_smc_finalise(addrspace_page);
  assert(result == KOM_ERR_SUCCESS);
  assert(address->state == KOM_ADDRSPACE_FINAL);
}

// helper function 
bool does_not_reference(uint64_t *unused, int64_t i, kom_secure_pageno_t pageno) {
  if (i < 0 || i >= KOM_SECURE_NPAGES) {
    return true;
  }
  return i == pageno || g_pagedb[i].addrspace != page_monvaddr(pageno);
}

/**
(define (spec-kom_smc_remove s page)
  (define addrspace_page ((state-pagedb.addrspace s) page))
  (cond
    [(state-enclave-mode s)
      (set-return! s komodo:KOM_ERR_ALREADY_ENTERED)]
    [(! (page-valid? page))
      (set-return! s komodo:KOM_ERR_INVALID_PAGENO)]
    [(page-free? s page)
      (set-return! s komodo:KOM_ERR_SUCCESS)]
    ; ; page is addrspace with non-zero refcount
    [(&& (page-typed? s page komodo:KOM_PAGE_ADDRSPACE)
         (! (bveq (state-addrspace.refcount s page) (bv 1 64))))
      (set-return! s komodo:KOM_ERR_PAGEINUSE)]
    [(&& (page-typed? s page komodo:KOM_PAGE_ADDRSPACE)
         (! (addrspace-state? s page komodo:KOM_ADDRSPACE_STOPPED)))
      (set-return! s komodo:KOM_ERR_NOT_STOPPED)]
    ; page is not addrspace and its addrspace is not stopped
    [(&& (! (page-typed? s page komodo:KOM_PAGE_ADDRSPACE))
         (! (addrspace-state? s addrspace_page komodo:KOM_ADDRSPACE_STOPPED)))
      (set-return! s komodo:KOM_ERR_NOT_STOPPED)]
    [else
      (sub1-state-addrspace.refcount! s addrspace_page)
      (set-state-page-refcnt! s (decr-refcnt (state-page-refcnt s) addrspace_page page))

      (update-state-pagedb.type! s page (bv komodo:KOM_PAGE_FREE 64))
      (update-state-pagedb.addrspace! s page (bv -1 64))

      (update-state-pgtable-present! s (list page page-index-valid?) #f)
      (update-state-pgtable-pn! s (list page page-index-valid?) (bv 0 64))
      (update-state-pgtable-perm! s (list page page-index-valid?) (bv 0 64))
      (update-state-pgtable-secure! s (list page page-index-valid?) #f)

      (set-return! s komodo:KOM_ERR_SUCCESS)]))
*/
void spec_kom_smc_remove_addrspace() {
  any(kom_secure_pageno_t, pageno);

  if (pageno < 0) {
    return;
  }

  if (enclave_mode) {
    int result = kom_smc_remove(pageno);
    assert(result == KOM_ERR_ALREADY_ENTERED);
    return;
  }

  if (pageno >= KOM_SECURE_NPAGES) {
    int result = kom_smc_remove(pageno);
    assert(result == KOM_ERR_INVALID_PAGENO);
    return;
  }
  if (g_pagedb[pageno].type == KOM_PAGE_FREE) {
    int result = kom_smc_remove(pageno);
    assert(result == KOM_ERR_SUCCESS);
    return;
  }

  assert(pageno < KOM_SECURE_NPAGES && g_pagedb[pageno].type != KOM_PAGE_FREE);

  if (g_pagedb[pageno].type != KOM_PAGE_ADDRSPACE) {
    return;
  }


  struct kom_addrspace *addrspace = (struct kom_addrspace *)&secure_pages[pageno];

  if (addrspace->refcount != 1) {
    int result = kom_smc_remove(pageno);
    assert(result == KOM_ERR_PAGEINUSE);
    return;
  }

  // TPot: In this path, knowing refcount == 1, we discard cases where other pages may refer to addrspace,
  // since we don't specify refcount correctness. Without this check, the POT still passes because the 
  // corretness of the implementation with respect to the functional correctness spec (spec.rkt) does 
  // not depend on refcount correctness. We require this check only to prove the additional meta-invariants 
  // about pgtable correctness.
  if (!forall_elem_(g_pagedb, does_not_reference, pageno)) {
    return;
  }


  if (addrspace->state != KOM_ADDRSPACE_STOPPED) {
    int result = kom_smc_remove(pageno);
    assert(result == KOM_ERR_NOT_STOPPED);
    return;
  }

  uint64_t old_refcnt = addrspace->refcount;

  int result = kom_smc_remove(pageno);
  assert(result == KOM_ERR_SUCCESS);
  assert(g_pagedb[pageno].type == KOM_PAGE_FREE);
  assert(g_pagedb[pageno].addrspace == NULL);

  assert(addrspace->refcount == old_refcnt - 1);
  assert(addrspace->refcount == 0);
}

void spec_kom_smc_remove_else() {
  any(kom_secure_pageno_t, pageno);

  if (pageno < 0) {
    return;
  }

  if (enclave_mode) {
    int result = kom_smc_remove(pageno);
    assert(result == KOM_ERR_ALREADY_ENTERED);
    return;
  }

  if (pageno >= KOM_SECURE_NPAGES) {
    int result = kom_smc_remove(pageno);
    assert(result == KOM_ERR_INVALID_PAGENO);
    return;
  }
  if (g_pagedb[pageno].type == KOM_PAGE_FREE) {
    int result = kom_smc_remove(pageno);
    assert(result == KOM_ERR_SUCCESS);
    return;
  }

  if (g_pagedb[pageno].type == KOM_PAGE_ADDRSPACE) {
    // this case is handled in spec_kom_smc_remove_addrspace
    return;
  }

  // uint64_t addrspace_page = g_pagedb[pageno].addrspace_page;
  // struct kom_addrspace *addrspace = (struct kom_addrspace *)&secure_pages[addrspace_page];
  struct kom_addrspace *addrspace = g_pagedb[pageno].addrspace;
  if (addrspace->state != KOM_ADDRSPACE_STOPPED) {
    int result = kom_smc_remove(pageno);
    assert(result == KOM_ERR_NOT_STOPPED);
    return;
  }

  uint64_t old_refcnt = addrspace->refcount;
  int result = kom_smc_remove(pageno);
  assert(result == KOM_ERR_SUCCESS);
  assert(g_pagedb[pageno].type == KOM_PAGE_FREE);
  assert(g_pagedb[pageno].addrspace == NULL);
  assert(addrspace->refcount == old_refcnt - 1);
}

/**
(define (spec-kom_smc_map_insecure s l3pt_page l3pt_index mapping
insecure_pageno) (define addrspace_page ((state-pagedb.addrspace s) l3pt_page))
  (cond
    [(! (insecure-page-valid? insecure_pageno))
      (set-return! s komodo:KOM_ERR_INVALID_PAGENO)]
    [(! (pte-index-valid? l3pt_index))
      (set-return! s komodo:KOM_ERR_INVALID_MAPPING)]
    [(! (page-typed? s l3pt_page komodo:KOM_PAGE_L3PTABLE))
      (set-return! s komodo:KOM_ERR_INVALID_PAGENO)]
    [(! (bvzero? ((state-pages s) l3pt_page l3pt_index)))
      (set-return! s komodo:KOM_ERR_ADDRINUSE)]
    [(! (addrspace-state? s addrspace_page komodo:KOM_ADDRSPACE_INIT))
      (set-return! s komodo:KOM_ERR_ALREADY_FINAL)]
    [else
      (define entry (pfn->pte (insecure_page->pfn insecure_pageno) (enclave-prot mapping)))
      (update-state-pages! s (list l3pt_page l3pt_index) entry)
      (update-state-pgtable-pn! s (list l3pt_page l3pt_index) insecure_pageno)
      (update-state-pgtable-present! s (list l3pt_page l3pt_index) #t)
      (update-state-pgtable-perm! s (list l3pt_page l3pt_index) mapping)
      (update-state-pgtable-secure! s (list l3pt_page l3pt_index) #f)


      (set-return! s komodo:KOM_ERR_SUCCESS)]))
*/
void spec_kom_smc_map_insecure() {
  any(kom_secure_pageno_t, l3pt_page);
  any(int64_t, l3pt_index);
  any(kom_secure_pageno_t, insecure_pageno);
  any(int64_t, mapping);

  if (l3pt_page < 0 || l3pt_index < 0 || insecure_pageno < 0 || mapping < 0) {
    return;
  }

  if (insecure_pageno >= KOM_INSECURE_NPAGES) {
    int result = kom_smc_map_insecure(l3pt_page, l3pt_index, mapping, insecure_pageno);
    assert(result == KOM_ERR_INVALID_PAGENO);
    return;
  }
  if (l3pt_index >= PTRS_PER_PTE) {
    int result = kom_smc_map_insecure(l3pt_page, l3pt_index, mapping, insecure_pageno);
    assert(result == KOM_ERR_INVALID_MAPPING);
    return;
  }
  if (l3pt_page >= KOM_SECURE_NPAGES || g_pagedb[l3pt_page].type != KOM_PAGE_L3PTABLE) {
    int result = kom_smc_map_insecure(l3pt_page, l3pt_index, mapping, insecure_pageno);
    assert(result == KOM_ERR_INVALID_PAGENO);
    return;
  }

  assert(l3pt_index < PTRS_PER_PTE);
  assert(l3pt_index >= 0);
  pte_t *l3pt = (pte_t *)&secure_pages[l3pt_page];
  if (l3pt[l3pt_index].pte != 0) {
    int result = kom_smc_map_insecure(l3pt_page, l3pt_index, mapping, insecure_pageno);
    assert(result == KOM_ERR_ADDRINUSE);
    return;
  }

  assert(l3pt_page < KOM_SECURE_NPAGES);
  // uint64_t addrspace_page = g_pagedb[l3pt_page].addrspace_page;
  struct kom_addrspace *addrspace = g_pagedb[l3pt_page].addrspace;
  if (addrspace == NULL) {
    int result = kom_smc_map_insecure(l3pt_page, l3pt_index, mapping, insecure_pageno);
    assert(result == KOM_ERR_INVALID_ADDRSPACE);
    return;
  }

  if (addrspace->state != KOM_ADDRSPACE_INIT) {
    int result = kom_smc_map_insecure(l3pt_page, l3pt_index, mapping, insecure_pageno);
    assert(result == KOM_ERR_ALREADY_FINAL);
    return;
  }

  int result = kom_smc_map_insecure(l3pt_page, l3pt_index, mapping, insecure_pageno);
  assert(result == KOM_ERR_SUCCESS);
  pte_t entry = pfn_pte(PFN_DOWN((uintptr_t)&_payload_start[insecure_pageno] + KOM_DIRECTMAP_VBASE),
                        __pgprot((mapping & KOM_MAPPING_RWX) | _PAGE_ENCLAVE));
  assert(l3pt[l3pt_index].pte == entry.pte);
  assert(g_pagedb[l3pt_page].type == KOM_PAGE_L3PTABLE);
}

/**
(define (spec-kom_smc_map_secure s page l3pt_page l3pt_index mapping content)
  (define addrspace_page ((state-pagedb.addrspace s) l3pt_page))
  (cond
    [(! (pte-index-valid? l3pt_index))
      (set-return! s komodo:KOM_ERR_INVALID_MAPPING)]
    [(|| (! (insecure-page-valid? content)) (! (page-typed? s l3pt_page komodo:KOM_PAGE_L3PTABLE)))
      (set-return! s komodo:KOM_ERR_INVALID_PAGENO)]
    [(! (bvzero? ((state-pages s) l3pt_page l3pt_index)))
      (set-return! s komodo:KOM_ERR_ADDRINUSE)]
    [(! (page-valid? page))
      (set-return! s komodo:KOM_ERR_INVALID_PAGENO)]
    [(! (page-free? s page))
      (set-return! s komodo:KOM_ERR_PAGEINUSE)]
    [(! (addrspace-state? s addrspace_page komodo:KOM_ADDRSPACE_INIT))
      (set-return! s komodo:KOM_ERR_ALREADY_FINAL)]
    [else
      (update-state-pagedb.type! s page (bv komodo:KOM_PAGE_DATA 64))
      (update-state-pagedb.addrspace! s page addrspace_page)

      (update-state-pages! s (list page pte-index-valid?) (bv 0 64))

      (add1-state-addrspace.refcount! s addrspace_page)
      (set-state-page-refcnt! s (incr-refcnt (state-page-refcnt s) addrspace_page page))

      (define entry (pfn->pte (page->pfn page) (enclave-prot mapping)))
      (update-state-pages! s (list l3pt_page l3pt_index) entry)
      (update-state-pgtable-pn! s (list l3pt_page l3pt_index) page)
      (update-state-pgtable-present! s (list l3pt_page l3pt_index) #t)
      (update-state-pgtable-perm! s (list l3pt_page l3pt_index) mapping)
      (update-state-pgtable-secure! s (list l3pt_page l3pt_index) #t)

      (define old-pages (state-pages s))
      (define old-insecure-pages (state-insecure-pages s))

      (set-state-pages! s
        (lambda (pageno idx)
          (cond
            [(&& (equal? pageno page) (bvult idx (bv 512 64)))
              (old-insecure-pages content idx)]
            [else (old-pages pageno idx)])))

      (set-return! s komodo:KOM_ERR_SUCCESS)]))
*/
void spec_kom_smc_map_secure_fail() {
  any(kom_secure_pageno_t, page);
  any(kom_secure_pageno_t, l3pt_page);
  any(int64_t, l3pt_index);
  any(kom_secure_pageno_t, content);
  any(int64_t, mapping);

  if (page < 0 || l3pt_page < 0 || l3pt_index < 0 || content < 0 || mapping < 0) {
    return;
  }

  if (l3pt_index >= PTRS_PER_PTE) {
    int result = kom_smc_map_secure(page, l3pt_page, l3pt_index, mapping, content);
    assert(result == KOM_ERR_INVALID_MAPPING);
    return;
  }
  if (content >= KOM_INSECURE_NPAGES) {
    int result = kom_smc_map_secure(page, l3pt_page, l3pt_index, mapping, content);
    assert(result == KOM_ERR_INVALID_PAGENO);
    return;
  }
  if (l3pt_page >= KOM_SECURE_NPAGES || g_pagedb[l3pt_page].type != KOM_PAGE_L3PTABLE) {
    int result = kom_smc_map_secure(page, l3pt_page, l3pt_index, mapping, content);
    assert(result == KOM_ERR_INVALID_PAGENO);
    return;
  }

  pte_t *l3pt = (pte_t *)page_monvaddr(l3pt_page);
  if (l3pt[l3pt_index].pte != 0) {
    int result = kom_smc_map_secure(page, l3pt_page, l3pt_index, mapping, content);
    assert(result == KOM_ERR_ADDRINUSE);
    return;
  }
  if (page >= KOM_SECURE_NPAGES) {
    int result = kom_smc_map_secure(page, l3pt_page, l3pt_index, mapping, content);
    assert(result == KOM_ERR_INVALID_PAGENO);
    return;
  }

  if (g_pagedb[page].type != KOM_PAGE_FREE) {
    int result = kom_smc_map_secure(page, l3pt_page, l3pt_index, mapping, content);
    assert(result == KOM_ERR_PAGEINUSE);
    return;
  }

  // uint64_t addrspace_page = g_pagedb[l3pt_page].addrspace_page;
  struct kom_addrspace *addrspace = g_pagedb[l3pt_page].addrspace;
  if (addrspace == NULL || g_pagedb[get_pgno(addrspace)].type != KOM_PAGE_ADDRSPACE) {
    int result = kom_smc_map_secure(page, l3pt_page, l3pt_index, mapping, content);
    assert(result == KOM_ERR_INVALID_ADDRSPACE);
    return;
  }

  // struct kom_addrspace *addrspace = (struct kom_addrspace *)&secure_pages[addrspace_page];
  if (addrspace->state != KOM_ADDRSPACE_INIT) {
    int result = kom_smc_map_secure(page, l3pt_page, l3pt_index, mapping, content);
    assert(result == KOM_ERR_ALREADY_FINAL);
    return;
  }
}

void spec_kom_smc_map_secure_success() {
  any(kom_secure_pageno_t, page);
  any(kom_secure_pageno_t, l3pt_page);
  any(int64_t, l3pt_index);
  any(kom_insecure_pageno_t, content);
  any(int64_t, mapping);

  if (page < 0 || l3pt_page < 0 || l3pt_index < 0 || content < 0 || mapping < 0) {
    return;
  }

  if (l3pt_index >= PTRS_PER_PTE || content >= KOM_INSECURE_NPAGES || l3pt_page >= KOM_SECURE_NPAGES ||
      g_pagedb[l3pt_page].type != KOM_PAGE_L3PTABLE) {
    return;
  }

  pte_t *l3pt = (pte_t *)&secure_pages[l3pt_page];
  if (l3pt[l3pt_index].pte != 0 || page >= KOM_SECURE_NPAGES || g_pagedb[page].type != KOM_PAGE_FREE) {
    return;
  }

  // uint64_t addrspace_page = g_pagedb[l3pt_page].addrspace_page;
  // struct kom_addrspace *address = (struct kom_addrspace *)&secure_pages[addrspace_page];
  struct kom_addrspace *addrspace = g_pagedb[l3pt_page].addrspace;
  if (addrspace == NULL || 
    g_pagedb[get_pgno(addrspace)].type != KOM_PAGE_ADDRSPACE ||
    addrspace->state != KOM_ADDRSPACE_INIT) {
    return;
  }

  uint64_t old_refcnt = addrspace->refcount;

  // assert(g_pagedb[addrspace_page].type == KOM_PAGE_ADDRSPACE);

  int result = kom_smc_map_secure(page, l3pt_page, l3pt_index, mapping, content);
  assert(result == KOM_ERR_SUCCESS);
  assert(addrspace->refcount == old_refcnt + 1);
  assert(g_pagedb[page].type == KOM_PAGE_DATA);
  assert(g_pagedb[page].addrspace == addrspace);
  pte_t entry =
      pfn_pte(PFN_DOWN((uintptr_t)&secure_pages[page]), __pgprot((mapping & KOM_MAPPING_RWX) | _PAGE_ENCLAVE));
  assert(l3pt[l3pt_index].pte == entry.pte);
  char *src = (void *)_payload_start + content * KOM_PAGE_SIZE + KOM_DIRECTMAP_VBASE;
  char *dst = (void *)secure_pages + page * KOM_PAGE_SIZE;
  assert(src[0] == dst[0]);
}

/**
(define (spec-kom_smc_init_l3ptable s page l2pt_page l2pt_index)
  (define addrspace_page ((state-pagedb.addrspace s) l2pt_page))
  (cond
    [(! (pte-index-valid? l2pt_index))
      (set-return! s komodo:KOM_ERR_INVALID_MAPPING)]
    [(! (page-typed? s l2pt_page komodo:KOM_PAGE_L2PTABLE))
      (set-return! s komodo:KOM_ERR_INVALID_PAGENO)]
    [(! (bvzero? ((state-pages s) l2pt_page l2pt_index)))
      (set-return! s komodo:KOM_ERR_ADDRINUSE)]
    [(! (page-valid? page))
      (set-return! s komodo:KOM_ERR_INVALID_PAGENO)]
    [(! (page-free? s page))
      (set-return! s komodo:KOM_ERR_PAGEINUSE)]
    [(! (addrspace-state? s addrspace_page komodo:KOM_ADDRSPACE_INIT))
      (set-return! s komodo:KOM_ERR_ALREADY_FINAL)]
    [else
      (update-state-pagedb.type! s page (bv komodo:KOM_PAGE_L3PTABLE 64))
      (update-state-pagedb.addrspace! s page addrspace_page)

      (update-state-pages! s (list page pte-index-valid?) (bv 0 64))
      (update-state-pgtable-pn! s (list page pte-index-valid?) (bv 0 64))
      (update-state-pgtable-present! s (list page pte-index-valid?) #f)
      (update-state-pgtable-perm! s (list page pte-index-valid?) (bv 0 64))
      (update-state-pgtable-secure! s (list page pte-index-valid?) #f)


      (add1-state-addrspace.refcount! s addrspace_page)
      (set-state-page-refcnt! s (incr-refcnt (state-page-refcnt s) addrspace_page page))

      (define entry (pfn->pte (page->pfn page) (bv komodo:_PAGE_TABLE 64)))
      (update-state-pages! s (list l2pt_page l2pt_index) entry)
      (update-state-pgtable-pn! s (list l2pt_page l2pt_index) page)
      (update-state-pgtable-present! s (list l2pt_page l2pt_index) #t)

      (set-return! s komodo:KOM_ERR_SUCCESS)]))
*/
void spec_kom_smc_init_l3ptable_fail() {
  any(kom_secure_pageno_t, page);
  any(kom_secure_pageno_t, l2pt_page);
  any(int64_t, l2pt_index);

  if (page < 0 || l2pt_page < 0 || l2pt_index < 0) {
    return;
  }

  if (l2pt_index >= KOM_PAGE_SIZE / sizeof(uint64_t)) {
    int result = kom_smc_init_l3ptable(page, l2pt_page, l2pt_index);
    assert(result == KOM_ERR_INVALID_MAPPING);
    return;
  }
  if (l2pt_page >= KOM_SECURE_NPAGES || g_pagedb[l2pt_page].type != KOM_PAGE_L2PTABLE) {
    int result = kom_smc_init_l3ptable(page, l2pt_page, l2pt_index);
    assert(result == KOM_ERR_INVALID_PAGENO);
    return;
  }
  pte_t *l2pt = (pte_t *)&secure_pages[l2pt_page];
  if (l2pt[l2pt_index].pte != 0) {
    int result = kom_smc_init_l3ptable(page, l2pt_page, l2pt_index);
    assert(result == KOM_ERR_ADDRINUSE);
    return;
  }
  if (page >= KOM_SECURE_NPAGES) {
    int result = kom_smc_init_l3ptable(page, l2pt_page, l2pt_index);
    assert(result == KOM_ERR_INVALID_PAGENO);
    return;
  }
  if (g_pagedb[page].type != KOM_PAGE_FREE) {
    int result = kom_smc_init_l3ptable(page, l2pt_page, l2pt_index);
    assert(result == KOM_ERR_PAGEINUSE);
    return;
  }

  // uint64_t addrspace_page = g_pagedb[l2pt_page].addrspace_page;
  struct kom_addrspace *addrspace = g_pagedb[l2pt_page].addrspace;

  // if (g_pagedb[addrspace_page].type != KOM_PAGE_ADDRSPACE) {
  if (addrspace == NULL || g_pagedb[get_pgno(addrspace)].type != KOM_PAGE_ADDRSPACE) {
    int result = kom_smc_init_l3ptable(page, l2pt_page, l2pt_index);
    assert(result == KOM_ERR_INVALID_ADDRSPACE);
    return;
  }

  // struct kom_addrspace *address = (struct kom_addrspace *)&secure_pages[addrspace_page];
  if (addrspace->state != KOM_ADDRSPACE_INIT) {
    int result = kom_smc_init_l3ptable(page, l2pt_page, l2pt_index);
    assert(result == KOM_ERR_ALREADY_FINAL);
    return;
  }
}

void spec_kom_smc_init_l3ptable_success() {
  any(kom_secure_pageno_t, page);
  any(kom_secure_pageno_t, l2pt_page);
  any(int64_t, l2pt_index);

  if (page < 0 || l2pt_page < 0 || l2pt_index < 0) {
    return;
  }

  if (l2pt_index >= KOM_PAGE_SIZE / sizeof(uint64_t) || l2pt_page >= KOM_SECURE_NPAGES ||
      g_pagedb[l2pt_page].type != KOM_PAGE_L2PTABLE || page >= KOM_SECURE_NPAGES ||
      g_pagedb[page].type != KOM_PAGE_FREE) {
    return;
  }
  pmd_t *l2pt = (pmd_t *)&secure_pages[l2pt_page];
  if (l2pt[l2pt_index].pmd != 0) {
    return;
  }

  // uint64_t addrspace_page = g_pagedb[l2pt_page].addrspace_page;
  // struct kom_addrspace *address = (struct kom_addrspace *)&secure_pages[addrspace_page];
  struct kom_addrspace *addrspace = g_pagedb[l2pt_page].addrspace;
  if (addrspace == NULL || addrspace->state != KOM_ADDRSPACE_INIT) {
    return;
  }

  uint64_t addrspace_pageno = ((uint64_t)addrspace - (uint64_t)secure_pages) / PAGE_SIZE;
  if (g_pagedb[addrspace_pageno].type != KOM_PAGE_ADDRSPACE) {
    return;
  }

  uint64_t old_refcnt = addrspace->refcount;

  int result = kom_smc_init_l3ptable(page, l2pt_page, l2pt_index);
  assert(result == KOM_ERR_SUCCESS);
  assert(g_pagedb[l2pt_page].addrspace != (void *)secure_pages + l2pt_page * PAGE_SIZE);

  assert(addrspace->refcount == old_refcnt + 1);
  assert(g_pagedb[page].type == KOM_PAGE_L3PTABLE);
  assert(g_pagedb[page].addrspace == addrspace);
  assert(l2pt[l2pt_index].pmd == pfn_pmd(PFN_DOWN((uintptr_t)&secure_pages[page]), __pgprot(_PAGE_TABLE)).pmd);
}

/**
(define (spec-kom_smc_init_l2ptable s page l1pt_page l1pt_index)
  (define addrspace_page ((state-pagedb.addrspace s) l1pt_page))
  (cond
    [(! (pte-index-valid? l1pt_index))
      (set-return! s komodo:KOM_ERR_INVALID_MAPPING)]
    [(! (page-typed? s l1pt_page komodo:KOM_PAGE_L1PTABLE))
      (set-return! s komodo:KOM_ERR_INVALID_PAGENO)]
    [(! (bvzero? ((state-pages s) l1pt_page l1pt_index)))
      (set-return! s komodo:KOM_ERR_ADDRINUSE)]
    [(! (page-valid? page))
      (set-return! s komodo:KOM_ERR_INVALID_PAGENO)]
    [(! (page-free? s page))
      (set-return! s komodo:KOM_ERR_PAGEINUSE)]
    [(! (addrspace-state? s addrspace_page komodo:KOM_ADDRSPACE_INIT))
      (set-return! s komodo:KOM_ERR_ALREADY_FINAL)]
    [else
      (update-state-pagedb.type! s page (bv komodo:KOM_PAGE_L2PTABLE 64))
      (update-state-pagedb.addrspace! s page addrspace_page)

      (update-state-pages! s (list page pte-index-valid?) (bv 0 64))
      (update-state-pgtable-pn! s (list page pte-index-valid?) (bv 0 64))
      (update-state-pgtable-present! s (list page pte-index-valid?) #f)
      (update-state-pgtable-perm! s (list page pte-index-valid?) (bv 0 64))
      (update-state-pgtable-secure! s (list page pte-index-valid?) #f)

      (add1-state-addrspace.refcount! s addrspace_page)
      (set-state-page-refcnt! s (incr-refcnt (state-page-refcnt s) addrspace_page page))

      (update-state-pages! s (list l1pt_page l1pt_index) (pfn->pte (page->pfnpage) (bv komodo:_PAGE_TABLE 64)))
      (update-state-pgtable-pn! s (list l1pt_pagel1pt_index) page)
      (update-state-pgtable-present! s (list l1pt_page l1pt_index) #t)

      (set-return! s komodo:KOM_ERR_SUCCESS)]))
*/
void spec_kom_smc_init_l2ptable() {
  any(kom_secure_pageno_t, page);
  any(kom_secure_pageno_t, l1pt_page);
  any(int64_t, l1pt_index);

  if (page < 0 || l1pt_page < 0 || l1pt_index < 0) {
    return;
  }

  if (l1pt_index >= PTRS_PER_PMD) {
    int result = kom_smc_init_l2ptable(page, l1pt_page, l1pt_index);
    assert(result == KOM_ERR_INVALID_MAPPING);
    return;
  }
  if (l1pt_page >= KOM_SECURE_NPAGES || g_pagedb[l1pt_page].type != KOM_PAGE_L1PTABLE) {
    int result = kom_smc_init_l2ptable(page, l1pt_page, l1pt_index);
    assert(result == KOM_ERR_INVALID_PAGENO);
    return;
  }
  pgd_t *l1pt = (pgd_t *)&secure_pages[l1pt_page];
  if (l1pt[l1pt_index].pgd != 0) {
    int result = kom_smc_init_l2ptable(page, l1pt_page, l1pt_index);
    assert(result == KOM_ERR_ADDRINUSE);
    return;
  }
  if (page >= KOM_SECURE_NPAGES) {
    int result = kom_smc_init_l2ptable(page, l1pt_page, l1pt_index);
    assert(result == KOM_ERR_INVALID_PAGENO);
    return;
  }
  if (g_pagedb[page].type != KOM_PAGE_FREE) {
    int result = kom_smc_init_l2ptable(page, l1pt_page, l1pt_index);
    assert(result == KOM_ERR_PAGEINUSE);
    return;
  }

  // uint64_t addrspace_page = g_pagedb[l1pt_page].addrspace_page;
  // if (g_pagedb[addrspace_page].type != KOM_PAGE_ADDRSPACE) {
  struct kom_addrspace *addrspace = g_pagedb[l1pt_page].addrspace;
  if (addrspace == NULL || g_pagedb[get_pgno(addrspace)].type != KOM_PAGE_ADDRSPACE) {
    int result = kom_smc_init_l2ptable(page, l1pt_page, l1pt_index);
    assert(result == KOM_ERR_INVALID_ADDRSPACE);
    return;
  }

  // struct kom_addrspace *address = (struct kom_addrspace *)&secure_pages[addrspace_page];
  if (addrspace->state != KOM_ADDRSPACE_INIT) {
    int result = kom_smc_init_l2ptable(page, l1pt_page, l1pt_index);
    assert(result == KOM_ERR_ALREADY_FINAL);
    return;
  }

  uint64_t old_refcnt = addrspace->refcount;

  int result = kom_smc_init_l2ptable(page, l1pt_page, l1pt_index);
  assert(result == KOM_ERR_SUCCESS);

  assert(g_pagedb[l1pt_page].addrspace != (void *)secure_pages + l1pt_page * PAGE_SIZE);
  assert(addrspace->refcount == old_refcnt + 1);
  assert(g_pagedb[page].type == KOM_PAGE_L2PTABLE);
  assert(g_pagedb[page].addrspace == addrspace);
  assert(l1pt[l1pt_index].pgd == pfn_pgd(PFN_DOWN((uintptr_t)&secure_pages[page]), __pgprot(_PAGE_TABLE)).pgd);
}

/**
(define (spec-kom_smc_init_dispatcher s page addrspace_page entrypoint)
  (cond
    [(! (page-typed? s addrspace_page komodo:KOM_PAGE_ADDRSPACE))
      (set-return! s komodo:KOM_ERR_INVALID_ADDRSPACE)]
    [(! (page-valid? page))
      (set-return! s komodo:KOM_ERR_INVALID_PAGENO)]
    [(! (page-free? s page))
      (set-return! s komodo:KOM_ERR_PAGEINUSE)]
    [(! (addrspace-state? s addrspace_page komodo:KOM_ADDRSPACE_INIT))
      (set-return! s komodo:KOM_ERR_ALREADY_FINAL)]
    [else
      (update-state-pagedb.type! s page (bv komodo:KOM_PAGE_DISPATCHER 64))
      (update-state-pagedb.addrspace! s page addrspace_page)

      (add1-state-addrspace.refcount! s addrspace_page)
      (set-state-page-refcnt! s (incr-refcnt (state-page-refcnt s) addrspace_page page))

      (update-state-pages! s (list page page-index-valid?) (bv 0 64))
      (update-state-dispatcher.mepc! s page entrypoint)
      (update-state-dispatcher.satp! s page (bvor (bv komodo:SATP_MODE_SV39 64)
                                            (page->pfn (state-addrspace.l1pt s addrspace_page))))
      (update-state-dispatcher.sie! s page (bvor (bv komodo:IE_SEIE 64)
                                                 (bv komodo:IE_STIE 64)
                                                 (bv komodo:IE_SSIE 64)))

      (set-return! s komodo:KOM_ERR_SUCCESS)]))
*/
void spec_kom_smc_init_dispatcher() {
  any(kom_secure_pageno_t, page);
  any(kom_secure_pageno_t, addrspace_page);
  any(uintptr_t, entrypoint);

  if (page < 0 || addrspace_page < 0) {
    return;
  }

  if (addrspace_page >= KOM_SECURE_NPAGES || g_pagedb[addrspace_page].type != KOM_PAGE_ADDRSPACE) {
    int result = kom_smc_init_dispatcher(page, addrspace_page, entrypoint);
    assert(result == KOM_ERR_INVALID_ADDRSPACE);
    return;
  }
  if (page >= KOM_SECURE_NPAGES) {
    int result = kom_smc_init_dispatcher(page, addrspace_page, entrypoint);
    assert(result == KOM_ERR_INVALID_PAGENO);
    return;
  }
  if (g_pagedb[page].type != KOM_PAGE_FREE) {
    int result = kom_smc_init_dispatcher(page, addrspace_page, entrypoint);
    assert(result == KOM_ERR_PAGEINUSE);
    return;
  }

  // struct kom_addrspace *address = (struct kom_addrspace *)&secure_pages[addrspace_page];
  // if (g_pagedb[addrspace_page].type != KOM_PAGE_ADDRSPACE) {
  struct kom_addrspace *addrspace = g_pagedb[addrspace_page].addrspace;
  if (addrspace == NULL) {
    int result = kom_smc_init_dispatcher(page, addrspace_page, entrypoint);
    assert(result == KOM_ERR_INVALID_ADDRSPACE);
    return;
  }

  if (addrspace->state != KOM_ADDRSPACE_INIT) {
    int result = kom_smc_init_dispatcher(page, addrspace_page, entrypoint);
    assert(result == KOM_ERR_ALREADY_FINAL);
    return;
  }

  uint64_t old_refcnt = addrspace->refcount;

  if (((struct kom_addrspace *)&secure_pages[addrspace_page])->l1pt_page >= KOM_SECURE_NPAGES) {
    return;
  }

  int result = kom_smc_init_dispatcher(page, addrspace_page, entrypoint);
  assert(result == KOM_ERR_SUCCESS);
  assert(g_pagedb[page].type == KOM_PAGE_DISPATCHER);
  assert(g_pagedb[page].addrspace == addrspace);
  assert(addrspace->refcount == old_refcnt + 1);
  struct kom_dispatcher *disp = (struct kom_dispatcher *)&secure_pages[page];
  assert(disp->mepc == entrypoint);
  assert(disp->satp ==
         (SATP_MODE_SV39 |
          PFN_DOWN((uintptr_t)&secure_pages[((struct kom_addrspace *)&secure_pages[addrspace_page])->l1pt_page])));
  assert(disp->sie == (IE_SEIE | IE_STIE | IE_SSIE));
}

/**
(define (spec-kom_smc_init_addrspace s addrspace_page l1pt_page)
  (cond
    [(bveq addrspace_page l1pt_page)
      (set-return! s komodo:KOM_ERR_INVALID_PAGENO)]
    [(! (&& (page-valid? addrspace_page) (page-valid? l1pt_page)))
      (set-return! s komodo:KOM_ERR_INVALID_PAGENO)]
    [(! (&& (page-free? s addrspace_page) (page-free? s l1pt_page)))
      (set-return! s komodo:KOM_ERR_PAGEINUSE)]
    [else
      (update-state-pagedb.type! s addrspace_page (bv komodo:KOM_PAGE_ADDRSPACE 64))
      (update-state-pagedb.addrspace! s addrspace_page addrspace_page)
      (update-state-pagedb.type! s l1pt_page (bv komodo:KOM_PAGE_L1PTABLE 64))
      (update-state-pagedb.addrspace! s l1pt_page addrspace_page)

      (update-state-pages! s (list addrspace_page page-index-valid?) (bv 0 64))
      (update-state-addrspace.l1pt! s addrspace_page l1pt_page)
      (update-state-addrspace.refcount! s addrspace_page (bv 2 64))
      (update-state-addrspace.state! s addrspace_page (bv komodo:KOM_ADDRSPACE_INIT 64))

      (update-state-pages! s (list l1pt_page pte-index-valid?) (bv 0 64))
      (update-state-pgtable-present! s (list l1pt_page pte-index-valid?) #f)
      (update-state-pgtable-pn! s (list l1pt_page pte-index-valid?) (bv 0 64))
      (update-state-pgtable-perm! s (list l1pt_page pte-index-valid?) (bv 0 64))
      (update-state-pgtable-secure! s (list l1pt_page pte-index-valid?) #f)

      (set-state-page-refcnt! s (incr-refcnt (state-page-refcnt s) addrspace_page addrspace_page))
      (set-state-page-refcnt! s (incr-refcnt (state-page-refcnt s) addrspace_page l1pt_page))

      (set-return! s komodo:KOM_ERR_SUCCESS)]))
*/
void spec_kom_smc_init_addrspace() {
  any(kom_secure_pageno_t, addrspace_page);
  any(kom_secure_pageno_t, l1pt_page);

  if (addrspace_page < 0 || l1pt_page < 0) {
    return;
  }

  if (addrspace_page == l1pt_page) {
    int result = kom_smc_init_addrspace(addrspace_page, l1pt_page);
    assert(result == KOM_ERR_INVALID_PAGENO);
    return;
  }
  if (addrspace_page >= KOM_SECURE_NPAGES || l1pt_page >= KOM_SECURE_NPAGES) {
    int result = kom_smc_init_addrspace(addrspace_page, l1pt_page);
    assert(result == KOM_ERR_INVALID_PAGENO);
    return;
  }

  assert(addrspace_page != l1pt_page);
  assert(addrspace_page >= 0 && addrspace_page < KOM_SECURE_NPAGES);
  assert(l1pt_page >= 0 && l1pt_page < KOM_SECURE_NPAGES);

  if (g_pagedb[addrspace_page].type != KOM_PAGE_FREE || g_pagedb[l1pt_page].type != KOM_PAGE_FREE) {
    int result = kom_smc_init_addrspace(addrspace_page, l1pt_page);
    assert(result == KOM_ERR_PAGEINUSE);
    return;
  }

  assert(addrspace_page != l1pt_page);
  assert(addrspace_page >= 0 && addrspace_page < KOM_SECURE_NPAGES);
  assert(l1pt_page >= 0 && l1pt_page < KOM_SECURE_NPAGES);
  assert(g_pagedb[addrspace_page].type == KOM_PAGE_FREE);
  assert(g_pagedb[l1pt_page].type == KOM_PAGE_FREE);

  struct kom_addrspace *addrspace = (void *)secure_pages + addrspace_page * KOM_PAGE_SIZE;

  int result = kom_smc_init_addrspace(addrspace_page, l1pt_page);
  assert(result == KOM_ERR_SUCCESS);

  assert(g_pagedb[addrspace_page].type == KOM_PAGE_ADDRSPACE);
  assert(g_pagedb[addrspace_page].addrspace == addrspace);
  assert(g_pagedb[l1pt_page].type == KOM_PAGE_L1PTABLE);
  assert(g_pagedb[l1pt_page].addrspace == addrspace);
  assert(g_pagedb[l1pt_page].addrspace != (void *)secure_pages + l1pt_page * PAGE_SIZE);

  assert(addrspace->l1pt_page == l1pt_page);
  assert(addrspace->refcount == 2);
  assert(addrspace->state == KOM_ADDRSPACE_INIT);
}