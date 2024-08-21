#pragma once

#include "monitor.h"
#include "tpot_primitives.h"
#include <asm/pmp.h>

extern struct kom_pagedb_entry g_pagedb[KOM_SECURE_NPAGES];
extern uint64_t secure_pages[KOM_SECURE_NPAGES][KOM_PAGE_SIZE / sizeof(uint64_t)] __aligned(KOM_PAGE_SIZE);
extern struct page_entry *_payload_start;

extern struct host_state host_state;
extern bool enclave_mode;
extern kom_secure_pageno_t g_cur_dispatcher_pageno;

static void *page_monvaddr(kom_secure_pageno_t pageno) {
  return (void *)secure_pages + pageno * KOM_PAGE_SIZE;
}