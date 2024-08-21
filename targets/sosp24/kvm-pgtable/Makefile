EXAMPLE=pgtable

CWD=$(shell pwd)
O?=$(CWD)/o.llvm-ir

SRC=.

SRC_LL=$(O)/src.ll

Z3_CACHE=./z3_cache

# -- tools -- #
MKDIR_P      := mkdir -p

LLVM_PREFIX  := "$(shell 'llvm-config-11' --bindir)/"
LLVM_CC      := $(LLVM_PREFIX)clang -target x86_64-pc-linux-gnu -Wno-initializer-overrides -Xclang -disable-O0-optnone
LLVM_OPT     := $(LLVM_PREFIX)opt -mem2reg -S
LLVM_LINK    := $(LLVM_PREFIX)llvm-link
# ----------- #

all: $(O)/specs-linked.ll

$(O)/specs-linked.ll: $(O)/specs.ll $(SRC_LL)
	$(LLVM_LINK) -o $@ -S $^

# -- build specs -- #
SPECS_CFLAGS	+=	-I$(SRC)
SPECS_CFLAGS	+= 	-I../../../klee-2.3/include/klee
SPECS_CFLAGS += 	-I../../../include

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

POTS += spec__kvm_set_table_pte
POTS += spec__kvm_set_valid_leaf_pte
POTS += spec__hyp_map_set_prot_attr

TARGET_SYSTEM = kvm-pgtable

include ../../../Makefile.common