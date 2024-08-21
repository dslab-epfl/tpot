/* SPDX-License-Identifier: GPL-2.0-only */
/* CP: originally at linux/arch/arm64/include/asm/page-def.h */
/*
 * Based on arch/arm/include/asm/page.h
 *
 * Copyright (C) 1995-2003 Russell King
 * Copyright (C) 2017 ARM Ltd.
 */




/* CP: removing everything, just fixing the PAGE_SHIFT and PAGE_SIZE values */
#define PAGE_SHIFT 12
#define PAGE_SIZE 4096
