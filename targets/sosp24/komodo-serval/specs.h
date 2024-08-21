#pragma once

#include "monitor.h"
#include "tpot_primitives.h"
#include <asm/pmp.h>

extern struct kom_pagedb_entry g_pagedb[KOM_SECURE_NPAGES];
extern uint64_t secure_pages[KOM_SECURE_NPAGES][KOM_PAGE_SIZE / sizeof(uint64_t)] __aligned(KOM_PAGE_SIZE);
extern uint64_t _payload_start[KOM_INSECURE_NPAGES][KOM_PAGE_SIZE / sizeof(uint64_t)];

extern struct host_state host_state;
extern bool enclave_mode;
extern kom_secure_pageno_t g_cur_dispatcher_pageno;
