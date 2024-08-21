CWD=$(shell pwd)
O?=$(CWD)/o.llvm-ir

SRC=../original

SRC_LL=$(O)/src.ll

Z3_CACHE=./z3_cache

ROOT_DIR     :=../../../..

# -- tools -- #
MKDIR_P      := mkdir -p

LLVM_PREFIX  := "$(shell 'llvm-config-11' --bindir)/"
LLVM_CC      := $(LLVM_PREFIX)clang -target x86_64-pc-linux-gnu -Wno-initializer-overrides -Xclang -disable-O0-optnone
LLVM_OPT     := $(LLVM_PREFIX)opt -mem2reg -S
LLVM_LINK    := $(LLVM_PREFIX)llvm-link
# ----------- #


# -- build symbtests -- #
SYMBTEST_CFLAGS	+=	-I$(SRC)
SYMBTEST_CFLAGS	+= 	-I$(ROOT_DIR)/klee-2.3/include/klee
SYMBTEST_CFLAGS += 	-I$(ROOT_DIR)/include

all: $(O)/specs-linked.ll

$(O)/specs-linked.ll: $(O)/symbtests.ll $(SRC_LL)
	$(LLVM_LINK) -o $@ -S $^

$(O)/symbtests.ll: specs.c spec_helpers.h
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC_IR)$(LLVM_CC) -g -o $@.no-opt -c -S -emit-llvm $(SYMBTEST_CFLAGS) -O0 $<
	$(LLVM_OPT) -o $@~ $@.no-opt
	$(Q)mv $@~ $@
# --------------------- #


# -- build src.ll -- #
$(SRC_LL): $(SRC)/early_alloc.c
	$(Q)$(MKDIR_P) $(@D)
	cd $(SRC) && $(LLVM_CC) -g -o $@.no-opt -c -S -emit-llvm $(SYMBTEST_CFLAGS) $(CFLAGS) -O0 $<
	$(LLVM_OPT) -o $@~ $@.no-opt
	$(Q)mv $@~ $@
# ------------------ #

POTS += spec__nr_pages
POTS += spec__alloc_page
POTS += spec__alloc_contig
POTS += init_spec__init

TARGET_SYSTEM = pkvm-early-alloc

include ../../../../Makefile.common