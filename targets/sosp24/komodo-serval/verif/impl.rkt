#lang rosette/safe

(require
  "state.rkt"
  serval/lib/core
  serval/spec/refcnt
  (prefix-in riscv: serval/riscv/objdump)
  (prefix-in komodo: "generated/monitors/komodo/verif/asm-offsets.rkt")
)

(provide (all-defined-out))


/*GLOBAL*/ (define (offset->index offset)
/*GLOBAL*/   (bvpointer (/ offset 8)))

/*GLOBAL*/ (define (mregions-abstract mregions)
/*GLOBAL*/   (define block-pagedb (find-block-by-name mregions 'g_pagedb))
/*GLOBAL*/   (define block-pages (find-block-by-name mregions 'secure_pages))
/*GLOBAL*/   (define block-enclave-mode (find-block-by-name mregions 'enclave_mode))
/*GLOBAL*/   (define block-host-state (find-block-by-name mregions 'host_state))
/*GLOBAL*/   (define block-current-dispatcher (find-block-by-name mregions 'g_cur_dispatcher_pageno))
/*GLOBAL*/   (define block-insecure-pages (find-block-by-name mregions '_payload_start))

/*GLOBAL*/   (define enclave-mode-i8 (mblock-iload block-enclave-mode null))
/*GLOBAL*/   (define enclave-mode (if (bveq enclave-mode-i8 (bv 0 8)) #f #t))

/*GLOBAL*/   (define current-dispatcher (mblock-iload block-current-dispatcher null))

/*GLOBAL*/   (define host-state
/*GLOBAL*/    (regs
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 'ra))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 'sp))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 'gp))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 'tp))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 't0))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 't1))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 't2))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 's0))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 's1))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 'a0))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 'a1))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 'a2))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 'a3))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 'a4))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 'a5))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 'a6))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 'a7))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 's2))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 's3))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 's4))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 's5))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 's6))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 's7))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 's8))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 's9))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 's10))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 's11))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 't3))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 't4))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 't5))
/*GLOBAL*/     (mblock-iload block-host-state (list 'regs 't6))
/*GLOBAL*/     (mblock-iload block-host-state (list 'satp))
/*GLOBAL*/     (mblock-iload block-host-state (list 'scause))
/*GLOBAL*/     (mblock-iload block-host-state (list 'scounteren))
/*GLOBAL*/     (mblock-iload block-host-state (list 'sepc))
/*GLOBAL*/     (mblock-iload block-host-state (list 'sscratch))
/*GLOBAL*/     (mblock-iload block-host-state (list 'sstatus))
/*GLOBAL*/     (mblock-iload block-host-state (list 'stvec))
/*GLOBAL*/     (mblock-iload block-host-state (list 'stval))
/*GLOBAL*/     (mblock-iload block-host-state (list 'mepc))
/*GLOBAL*/     (mblock-iload block-host-state (list 'sip))
/*GLOBAL*/     (mblock-iload block-host-state (list 'sie))
   ))

/*GLOBAL*/   (define page-refcnt (make-havoc-refcnt))
/*GLOBAL*/   (define-symbolic* current-addrspace (bitvector 64))
/*GLOBAL*/   (define-symbolic* pgtable-pn pgtable-perm (~> (bitvector 64) (bitvector 64) (bitvector 64)))
/*GLOBAL*/   (define-symbolic* pgtable-present pgtable-secure (~> (bitvector 64) (bitvector 64) boolean?))

         ; regs
/*GLOBAL*/   (state (zero-regs)
         ; pagedb.type
/*GLOBAL*/          (lambda (pageno)
/*GLOBAL*/            (mblock-iload block-pagedb (list pageno 'type)))
         ; pagedb.addrspace
/*GLOBAL*/          (lambda (pageno)
/*GLOBAL*/            (mblock-iload block-pagedb (list pageno 'addrspace_page)))
         ; pages
/*GLOBAL*/          (lambda (pageno index)
/*GLOBAL*/            (mblock-iload block-pages (list pageno index)))
         ; insecure pages
/*GLOBAL*/          (lambda (pageno index)
/*GLOBAL*/            (mblock-iload block-insecure-pages (list pageno index)))
/*GLOBAL*/          enclave-mode
/*GLOBAL*/          host-state
/*GLOBAL*/          current-dispatcher
/*GLOBAL*/          current-addrspace
/*GLOBAL*/          page-refcnt
/*GLOBAL*/          pgtable-pn
/*GLOBAL*/          pgtable-present
/*GLOBAL*/          pgtable-perm
/*GLOBAL*/          pgtable-secure))


/*GLOBAL*/ (define (mregions-invariants mregions)
/*GLOBAL*/   (define block-pagedb (find-block-by-name mregions 'g_pagedb))
/*GLOBAL*/   (define block-pages (find-block-by-name mregions 'secure_pages))
/*GLOBAL*/   (define block-host-state (find-block-by-name mregions 'host_state))
/*GLOBAL*/   (define block-current-dispatcher (find-block-by-name mregions 'g_cur_dispatcher_pageno))
/*GLOBAL*/   (define block-enclave-mode (find-block-by-name mregions 'enclave_mode))

/*GLOBAL*/   (define enclave-mode-i8 (mblock-iload block-enclave-mode null))
/*GLOBAL*/   (define enclave-mode (if (bveq enclave-mode-i8 (bv 0 8)) #f #t))

/*GLOBAL*/   (define current-dispatcher (mblock-iload block-current-dispatcher null))

/*GLOBAL*/   (define (pageno->pagedb.type pageno)
/*GLOBAL*/     (mblock-iload block-pagedb (list pageno 'type)))

/*GLOBAL*/   (define (pageno->pagedb.addrspace_page pageno)
/*GLOBAL*/     (mblock-iload block-pagedb (list pageno 'addrspace_page)))

/*GLOBAL*/   (define (pageno->addrspace.l1pt_page pageno)
/*GLOBAL*/     (mblock-iload block-pages (list pageno (offset->index komodo:KOM_ADDRSPACE_L1PT_PAGE))))

/*GLOBAL*/   (define (pageno->dispatcher.sie pageno)
/*GLOBAL*/     (mblock-iload block-pages (list pageno (bvpointer komodo:KOM_DISPATCHER_SIE))))
/*GLOBAL*/   (define (pageno->dispatcher.sip pageno)
/*GLOBAL*/     (mblock-iload block-pages (list pageno (bvpointer komodo:KOM_DISPATCHER_SIP))))
/*GLOBAL*/   (define (pageno->dispatcher.sstatus pageno)
    (mblock-iload block-pages (list pageno (bvpointer komodo:KOM_DISPATCHER_SSTATUS))))
/*GLOBAL*/ 
/*GLOBAL*/   (define (impl-page-typed? pageno type)
/*GLOBAL*/     (&& (page-valid? pageno)
/*GLOBAL*/         (bveq (pageno->pagedb.type pageno) (bv type 64))))

/*GLOBAL*/   (define (impl-page-nonfree? pageno)
/*GLOBAL*/     (&& (page-valid? pageno)
/*GLOBAL*/         (! (bveq (pageno->pagedb.type pageno) (bv komodo:KOM_PAGE_FREE 64)))))

/*GLOBAL*/   (define-symbolic pageno (bitvector 64))

  ; Use page-valid? only here, as using types complicates the RI (esp. for remove).
/*GLOBAL*/   (&&
/*GLOBAL*/     ; pagedb[pageno].addrspace_page is valid if pageno is not free
/*GLOBAL*/     (forall (list pageno)
/*GLOBAL*/             (=> (impl-page-nonfree? pageno)
/*GLOBAL*/                 (page-valid? (pageno->pagedb.addrspace_page pageno))))
    ; addrspace.l1pt_page is valid
/*GLOBAL*/     (forall (list pageno)
/*GLOBAL*/             (=> (impl-page-typed? pageno komodo:KOM_PAGE_ADDRSPACE)
/*GLOBAL*/                 (page-valid? (pageno->addrspace.l1pt_page pageno))))
/*GLOBAL*/     (forall (list pageno)
/*GLOBAL*/             (=> (impl-page-typed? pageno komodo:KOM_PAGE_ADDRSPACE)
/*GLOBAL*/                 (bveq pageno (pageno->pagedb.addrspace_page pageno))))
/*GLOBAL*/     (forall (list pageno)
/*GLOBAL*/             (=> (impl-page-typed? pageno komodo:KOM_PAGE_DISPATCHER)
/*GLOBAL*/                 (&&
/*GLOBAL*/                   (bveq (bvand (bvnot riscv:sstatus-mask) (pageno->dispatcher.sstatus pageno)) (bv 0 64))
/*GLOBAL*/                   (bveq (bvand (bvnot riscv:sie-mask) (pageno->dispatcher.sie pageno)) (bv 0 64))
/*GLOBAL*/                   (bveq (bvand (bvnot riscv:sip-mask) (pageno->dispatcher.sip pageno)) (bv 0 64)))))

/*GLOBAL*/     (page-valid? current-dispatcher)
/*GLOBAL*/     (=> enclave-mode
/*GLOBAL*/       (impl-page-typed? current-dispatcher komodo:KOM_PAGE_DISPATCHER))
/*GLOBAL*/     (bveq (bvand (bvnot riscv:sstatus-mask) (mblock-iload block-host-state (list 'sstatus))) (bv 0 64))
/*GLOBAL*/     (bveq (bvand (bvnot riscv:sie-mask) (mblock-iload block-host-state (list 'sie))) (bv 0 64))
/*GLOBAL*/     (bveq (bvand (bvnot riscv:sip-mask) (mblock-iload block-host-state (list 'sip))) (bv 0 64))
))
