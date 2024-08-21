#include "asm/page.h"
#include "monitor.h"
#include "specs.h"
#include <stdint.h>

struct page_entry *real_address; // shortcut for (void *)_payload_start + KOM_DIRECTMAP_VBASE
//helper
static kom_secure_pageno_t get_pgno(struct kom_addrspace *ptr) {
  return (kom_secure_pageno_t)(((uint64_t)ptr - (uint64_t)&secure_pages[0][0]) / PAGE_SIZE);
}

bool inv__payload_start_alloc() {
  return ((void *)_payload_start + KOM_DIRECTMAP_VBASE == real_address) &&
         names_obj(real_address, struct page_entry[KOM_INSECURE_NPAGES]);
}

bool addrspace_page_valid(uint64_t *unused, int64_t i) {
  if (i < 0 || i >= KOM_SECURE_NPAGES)
    return true;
  struct kom_pagedb_entry *ptr = &g_pagedb[i];
  struct kom_addrspace *page = (struct kom_addrspace *)&secure_pages[i];

  if (ptr->type == KOM_PAGE_FREE) {
    return true;
  }

  if (ptr->addrspace < 0) {
    return false;
  }

  // [invariants.rkt]
  // ; The owner of a non-free page is a valid page
  // (forall (list pageno)
  //   (=> (page-nonfree? pageno)
  //     (page-valid? (page->addrspace pageno))))
  // [impl.rkt]
  // ; pagedb[pageno].addrspace_page is valid if pageno is not free
  // (forall (list pageno)
  //           (=> (impl-page-nonfree? pageno)
  //               (page-valid? (pageno->pagedb.addrspace_page pageno))))
  void *sp_start = (void *)&secure_pages[0][0];
  if (ptr->type != KOM_PAGE_FREE
      // && ptr->addrspace_page >= KOM_SECURE_NPAGES
      && (
             // not null
             (void *)ptr->addrspace == NULL
             // should fall in secure_pages
             || (void *)ptr->addrspace < sp_start ||
             (void *)ptr->addrspace > sp_start + (KOM_SECURE_NPAGES - 1) * PAGE_SIZE
             // should be page aligned
             || ((void *)ptr->addrspace - sp_start) % PAGE_SIZE != 0
             //
             )
      //
  ) {
    return false;
  }
  struct kom_addrspace *address = (struct kom_addrspace *)&secure_pages[i];

  if (ptr->type == KOM_PAGE_ADDRSPACE) {
    // [invariants.rkt]
    // ; Every addrspace owns itself
    // (forall (list pageno)
    //   (=> (page-typed? pageno komodo:KOM_PAGE_ADDRSPACE)
    //     (bveq pageno (page->addrspace pageno))))
    // [impl.rkt]
    // (forall (list pageno)
    //         (=> (impl-page-typed? pageno komodo:KOM_PAGE_ADDRSPACE)
    //             (bveq pageno (pageno->pagedb.addrspace_page pageno))))
    if (ptr->addrspace != (void *)secure_pages + i * PAGE_SIZE) {
      return false;
    }
    // [impl.rkt]
    // ; addrspace.l1pt_page is valid
    //   (forall (list pageno)
    //           (=> (impl-page-typed? pageno komodo:KOM_PAGE_ADDRSPACE)
    //               (page-valid? (pageno->addrspace.l1pt_page pageno))))
    if (address->l1pt_page < 0 || address->l1pt_page >= KOM_SECURE_NPAGES) {
      return false;
    }
  }

  if (ptr->type != KOM_PAGE_ADDRSPACE && ptr->type != KOM_PAGE_FREE) {
    // forall (list pageno)
    //   (=> (page-nonfree? pageno)
    //     (page-typed? (page->addrspace pageno) komodo:KOM_PAGE_ADDRSPACE)))))
    if (g_pagedb[get_pgno(ptr->addrspace)].type != KOM_PAGE_ADDRSPACE) {

      return false;
    }
    // no self-references
    if (ptr->addrspace == (void *)secure_pages + i * PAGE_SIZE) {
      return false;
    }
  }

  return true;
}

bool inv__addrspace_page_valid() {
  return forall_elem_(g_pagedb, addrspace_page_valid);
}

bool insecure_l1page_valid(uint64_t *unused, int64_t i) {
  if (i < 0 || i >= KOM_INSECURE_NPAGES)
    return true;
  struct kom_addrspace *ptr = (struct kom_addrspace *)&real_address[i];
  return ptr->l1pt_page < KOM_INSECURE_NPAGES;
}

bool inv__insecure_page_valid() {
  return forall_elem_(real_address, insecure_l1page_valid);
}

bool inv__current_dispatcher_valid() {
  // [invariants.rkt]
  // ; The current dispatcher is a valid page
  // (page-valid? current-dispatcher)
  // [impl.rkt]
  // (page-valid? current-dispatcher)
  if (g_cur_dispatcher_pageno >= KOM_SECURE_NPAGES || g_cur_dispatcher_pageno < 0) {
    return false;
  }

  // [invariants.rkt]
  // ; When in enclave mode, the current dispatcher page is the right type
  // (=> enclave-mode
  //   (page-typed? current-dispatcher komodo:KOM_PAGE_DISPATCHER))
  // [impl.rkt]
  // (=> enclave-mode
  //   (impl-page-typed? current-dispatcher komodo:KOM_PAGE_DISPATCHER))
  if (enclave_mode && g_pagedb[g_cur_dispatcher_pageno].type != KOM_PAGE_DISPATCHER) {
    return false;
  }
  return true;
}

// [riscv/base.rkt]
#define SSTATUS_MASK  0x80000003000DE133
#define SIE_MASK      0x0000000000000333
#define SIP_MASK      0x0000000000000333

bool dispatcher_page_valid(uint64_t *unused, int64_t i) {
  if (i < 0 || i >= KOM_SECURE_NPAGES)
    return true;
  struct kom_pagedb_entry *ptr = &g_pagedb[i];
  // [impl.rkt]
  // (forall (list pageno)
  //           (=> (impl-page-typed? pageno komodo:KOM_PAGE_DISPATCHER)
  //               (&&
  //                 (bveq (bvand (bvnot riscv:sstatus-mask) (pageno->dispatcher.sstatus pageno)) (bv 0 64))
  //                 (bveq (bvand (bvnot riscv:sie-mask) (pageno->dispatcher.sie pageno)) (bv 0 64))
  //                 (bveq (bvand (bvnot riscv:sip-mask) (pageno->dispatcher.sip pageno)) (bv 0 64)))))
  if (ptr->type == KOM_PAGE_DISPATCHER) {
    struct kom_dispatcher *disp = (struct kom_dispatcher *)&secure_pages[i];
    return (disp->sstatus & ~SSTATUS_MASK == 0)
        && (disp->sie & ~SIE_MASK == 0)
        && (disp->sip & ~SIP_MASK == 0);
  }
}

bool inv__dispatcher_pages_valid() {
  // [impl.rkt]
  // (forall (list pageno)
  //   (=> (page-typed? pageno komodo:KOM_PAGE_DISPATCHER)
  //     (page-valid? (page->addrspace pageno))))
  return forall_elem_(g_pagedb, dispatcher_page_valid);
}

bool inv__cstate_valid() {
  // [impl.rkt]
  // (bveq (bvand (bvnot riscv:sstatus-mask) (mblock-iload block-host-state (list 'sstatus))) (bv 0 64))
  // (bveq (bvand (bvnot riscv:sie-mask) (mblock-iload block-host-state (list 'sie))) (bv 0 64))
  // (bveq (bvand (bvnot riscv:sip-mask) (mblock-iload block-host-state (list 'sip))) (bv 0 64))
  return ((sstatus_cstate & ~SSTATUS_MASK) == 0)
      && ((sie_cstate & ~SIE_MASK) == 0)
      && ((sip_cstate & ~SIP_MASK) == 0);
}

// helper
bool pgtable_ok(int64_t pgno, int64_t index) {
  if (pgno < 0 || pgno >= KOM_SECURE_NPAGES)
    return false;
  if (index < 0 || index >= PTRS_PER_PTE) // PTRS_PER_PMD?
    return false;

  kom_secure_pageno_t addrspace_pgno = get_pgno(g_pagedb[pgno].addrspace);

  return g_pagedb[addrspace_pgno].type == KOM_PAGE_ADDRSPACE &&
          ((struct kom_addrspace *)&secure_pages[addrspace_pgno])->state != KOM_ADDRSPACE_STOPPED;
}

// We use an unconstrainted fresh variable to ensure the invariants applies to all indices.
// This works because the conditions specified here are not necessary for the POTs to pass, so they
// serve as specifications and not proofs. To prove that the invariant is maintaied for an arbitrary index,
// it is sufficient to assume the invariant for that specific index.
// Similarly, in Serval case study, these conditions are not a part of the representation invariant.
int64_t any_pgtable_idx;

bool page_table_valid(uint64_t *unused, int64_t i) {
  if (i < 0 || i >= KOM_SECURE_NPAGES)
    return true;

  struct kom_pagedb_entry *ptr = &g_pagedb[i];
  // [invariants.rkt]
  //  ; l1ptable is correct
  // (forall (list pageno)
  //   (=> (&& (page-typed? pageno komodo:KOM_PAGE_ADDRSPACE)
  //           (! (addrspace-state? st pageno komodo:KOM_ADDRSPACE_STOPPED)))
  //     (&& (page-typed? (state-addrspace.l1pt st pageno) komodo:KOM_PAGE_L1PTABLE)
  //         (bveq pageno (page->addrspace (state-addrspace.l1pt st pageno))))))

  struct kom_addrspace *address = (struct kom_addrspace *)&secure_pages[i];

  if (ptr->type == KOM_PAGE_ADDRSPACE && address->state != KOM_ADDRSPACE_STOPPED) {
    if (g_pagedb[address->l1pt_page].type != KOM_PAGE_L1PTABLE) {
      return false;
    }
    if (address->l1pt_page != i) {
      return false;
    }
  }

  // [invariants.rkt]
  // ; L1 points to L2
  // (forall (list pageno index)
  //   (=> (&& (pgtable-ok? pageno index)
  //           (pgtable-present pageno index)
  //           (page-typed? pageno komodo:KOM_PAGE_L1PTABLE))
  //     (&& (page-typed? (pgtable-pn pageno index) komodo:KOM_PAGE_L2PTABLE)
  //         (bveq (page->addrspace pageno) (page->addrspace (pgtable-pn pageno index))))))
  if (ptr->type == KOM_PAGE_L1PTABLE && 
      pgtable_ok(i, any_pgtable_idx)) {
    pgd_t pgd = ((pgd_t *) page_monvaddr(i))[any_pgtable_idx];
    if (pgd_present(pgd)) {
      unsigned long pfn = pgd_pfn(pgd);
      if ( pfn < 0 || pfn >= KOM_SECURE_NPAGES) {
        return false;
      }
      struct kom_pagedb_entry *l2 = &g_pagedb[pfn];
      if (l2->type != KOM_PAGE_L2PTABLE) {
        return false;
      }
      if (l2->addrspace != ptr->addrspace) {
        return false;
      }
    }
  }

  // [invariants.rkt]
  // ; L2 points to L3
  // (forall (list pageno index)
  //     (=> (&& (pgtable-ok? pageno index)
  //             (pgtable-present pageno index)
  //             (page-typed? pageno komodo:KOM_PAGE_L2PTABLE))
  //       (&& (page-typed? (pgtable-pn pageno index) komodo:KOM_PAGE_L3PTABLE)
  //           (bveq (page->addrspace pageno) (page->addrspace (pgtable-pn pageno index))))))
  if (ptr->type == KOM_PAGE_L2PTABLE && 
      pgtable_ok(i, any_pgtable_idx)) {
    pmd_t pmd = ((pmd_t *) page_monvaddr(i))[any_pgtable_idx];
    if (pmd_present(pmd)) {
      unsigned long pfn = pmd_pfn(pmd);
      if ( pfn < 0 || pfn >= KOM_SECURE_NPAGES) {
        return false;
      }
      struct kom_pagedb_entry *l3 = &g_pagedb[pfn];
      if (l3->type != KOM_PAGE_L3PTABLE) {
        return false;
      }
      if (l3->addrspace != ptr->addrspace) {
        return false;
      }
    }
  }

  // [invariants.rkt]
  // ; L3 secure page ok
  // (forall (list pageno index)
  //     (=> (&& (pgtable-ok? pageno index)
  //             (pgtable-present pageno index)
  //             (page-typed? pageno komodo:KOM_PAGE_L3PTABLE)
  //             (pgtable-secure pageno index))
  //       (&& (page-typed? (pgtable-pn pageno index) komodo:KOM_PAGE_DATA)
  //           (bveq (page->addrspace pageno) (page->addrspace (pgtable-pn pageno index))))))
  // ; L3 insecure page ok
  //   (forall (list pageno index)
  //     (=> (&& (pgtable-ok? pageno index)
  //             (pgtable-present pageno index)
  //             (page-typed? pageno komodo:KOM_PAGE_L3PTABLE)
  //             (! (pgtable-secure pageno index)))
  //       (insecure-page-valid? (pgtable-pn pageno index))))
  if (ptr->type == KOM_PAGE_L3PTABLE && 
      pgtable_ok(i, any_pgtable_idx)) {
    pte_t pte = ((pte_t *) page_monvaddr(i))[any_pgtable_idx];
    if (pte_present(pte)) {
      unsigned long pfn = pte_pfn(pte);
      if ( pfn < 0 || pfn >= KOM_SECURE_NPAGES) {
        return false;
      }
      struct kom_pagedb_entry *p = &g_pagedb[pfn];
      if (pte_pfn(pte) >= KOM_INSECURE_NPAGES) {
        // page is secure
        if (p->type != KOM_PAGE_DATA) {
          return false;
        }
        if (p->addrspace != ptr->addrspace) {
          return false;
        }
      } else {
        // the Serval spec only relates the < KOM_INSECURE_NPAGES condition to
        // state-pgtable-secure predicate over asbstract state, and asserts no othe conditions.
        /* nop */
      }
    }
  }

  // [invariants.rkt]
  // ; Pages that are not page tables do not have present entries
  //   (forall (list pageno index)
  //     (=> (&& (page-valid? pageno)
  //             (page-index-valid? index)
  //             (! (page-typed? pageno komodo:KOM_PAGE_L1PTABLE))
  //             (! (page-typed? pageno komodo:KOM_PAGE_L2PTABLE))
  //             (! (page-typed? pageno komodo:KOM_PAGE_L3PTABLE)))
  //       (&& (! (pgtable-present pageno index))
  //           (bveq (pgtable-pn pageno index) (bv 0 64)))))
  
  // This part of the invariant only concerns ghost state. pgtable-present is an abstract function.
  // E.g., see serval's spec-kom_smc_remove. It updates pgtable ghost state even though the function
  // itself does not update the page table.
  // In the implementation state, pages that are not page tables may have bits that corrsepond to
  // present entries set.

  // [invariants.rkt]
  // ; Only leaves have permission bits or secure bit set
  //   (forall (list pageno index)
  //     (=> (&& (page-valid? pageno)
  //             (page-index-valid? index)
  //             (! (page-typed? pageno komodo:KOM_PAGE_L3PTABLE)))
  //       (&& (! (pgtable-secure pageno index))
  //           (bveq (pgtable-perm pageno index) (bv 0 64)))))

  // Same here. This only concerns ghost state.

  return true;
}

bool inv__page_table_valid() {
  return forall_elem_(g_pagedb, page_table_valid);
}