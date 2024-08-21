EXAMPLE=structs/index_pool

CWD=$(shell pwd)
O?=$(CWD)/o.llvm-ir

SRC=$(CWD)/../../env/src
INC=$(CWD)/../../env/include

SRC_LL=$(O)/src.ll

Z3_CACHE=./z3_cache

ROOT_DIR     :=../../../../..

# -- tools -- #
MKDIR_P      := mkdir -p

LLVM_PREFIX  := "$(shell 'llvm-config-11' --bindir)/"
LLVM_CC      := $(LLVM_PREFIX)clang -target x86_64-pc-linux-gnu -Wno-initializer-overrides -Xclang -disable-O0-optnone
LLVM_OPT     := $(LLVM_PREFIX)opt -mem2reg -S
LLVM_LINK    := $(LLVM_PREFIX)llvm-link
# ----------- #

all: $(O)/specs-linked.ll

$(O)/specs-linked.ll: $(O)/specs.ll $(SRC_LL) $(O)/tpot_models.ll
	$(LLVM_LINK) -o $@ -S $^

# -- build specs -- #
SPECS_CFLAGS	+=	-I$(INC)
SPECS_CFLAGS	+= 	-I$(ROOT_DIR)/klee-2.3/include/klee
SPECS_CFLAGS += 	-I$(ROOT_DIR)/include

$(O)/specs.ll: specs.c
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC_IR)$(LLVM_CC) -g -o $@.no-opt -c -S -emit-llvm $(SPECS_CFLAGS) -O0 $<
	$(LLVM_OPT) -o $@~ $@.no-opt
	$(Q)mv $@~ $@
# --------------------- #

# -- build src.ll -- #
$(SRC_LL): $(SRC)/$(EXAMPLE).c
	$(Q)$(MKDIR_P) $(@D)
	cd $(SRC) && $(LLVM_CC) -g -o $@.no-opt -c -S -emit-llvm $(CFLAGS) $(SPECS_CFLAGS) $<
	$(LLVM_OPT) -o $@~ $@.no-opt
	$(Q)mv $@~ $@
# ------------------ #

# -- build tpot_models.ll -- #
$(O)/tpot_models.ll: tpot_models.c
	$(Q)$(MKDIR_P) $(@D)
	$(LLVM_CC) -g -o $@.no-opt -c -S -emit-llvm $(CFLAGS) $(SPECS_CFLAGS) $<
	$(LLVM_OPT) -o $@~ $@.no-opt
	$(Q)mv $@~ $@
# ------------------ #


POTS += spec__refresh
POTS += spec__borrow
POTS += spec__used
POTS += spec__return
POTS += init_spec__alloc

TARGET_SYSTEM = vigor-allocator

include ../../../../../Makefile.common