include config.mk
include Makefile.lib

# no built-in rules and variables
MAKEFLAGS       += --no-builtin-rules --no-builtin-variables

BASE_CFLAGS     += -ffreestanding
BASE_CFLAGS     += -fno-stack-protector
BASE_CFLAGS     += -fno-strict-aliasing
# make it simpler for symbolic execution to track PC
BASE_CFLAGS     += -fno-jump-tables
# no unaligned memory accesses
# BASE_CFLAGS     += -mstrict-align
BASE_CFLAGS     += -g -O$(OLEVEL)
BASE_CFLAGS     += -Wall -MD -MP
#TPot
# BASE_CFLAGS 			+= -Wno-initializer-overrides -Xclang -disable-O0-optnone

CONFIG_CFLAGS   += -DCONFIG_NR_CPUS=$(CONFIG_NR_CPUS)
CONFIG_CFLAGS   += -DCONFIG_BOOT_CPU=$(CONFIG_BOOT_CPU)
CONFIG_CFLAGS   += -DCONFIG_DRAM_START=$(CONFIG_DRAM_START)
CONFIG_CFLAGS   += -DCONFIG_VERIFICATION=$(CONFIG_VERIFICATION)

CFLAGS          += $(BASE_CFLAGS) $(CONFIG_CFLAGS)
CFLAGS          += -mcmodel=medany
# no floating point
CFLAGS          += -mabi=lp64
CFLAGS          += -ffunction-sections -fdata-sections
CFLAGS          += -fno-PIE
CFLAGS          += -I include
CFLAGS          += -march=rv64ima

USER_CFLAGS     += $(BASE_CFLAGS)
USER_CFLAGS     += -I include/uapi

LDFLAGS         += -nostdlib
LDFLAGS         += --gc-sections

UBSAN_CFLAGS    += -fsanitize=integer-divide-by-zero
UBSAN_CFLAGS    += -fsanitize=shift
UBSAN_CFLAGS    += -fsanitize=signed-integer-overflow

include bios/bios.mk
include kernel/kernel.mk
include komodo.mk

all: $(O)/specs-linked.ll

.DEFAULT_GOAL = all

# for asm-offsets.S
$(O)/%.S: %.c
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC)$(CC) -o $@ $(filter-out -g,$(CFLAGS)) -S $<

# include zeros for bss in the binary
%.bin: %.elf
	$(QUIET_GEN)$(OBJCOPY) -O binary --set-section-flags .bss=alloc,load,contents $< $@

# --prefix-addresses prints the complete address on each line
%.asm: %.elf
	$(QUIET_GEN)$(OBJDUMP) -M no-aliases --prefix-addresses -w -f -d -z --show-raw-insn "$<" > "$@"

# sort addresses for *.map.rkt
%.map: %.elf
	$(QUIET_GEN)$(NM) --print-size --numeric-sort "$<" > "$@"

%.bin.o: %.bin bbl/payload.S
	$(QUIET_CC)$(CC) -o $@ -c -mabi=lp64 -DBBL_PAYLOAD='"$<"' bbl/payload.S

%.bbl: %.bin.o $(wildcard bbl/*.o) bbl/libmachine.a bbl/libsoftfloat.a bbl/libutil.a
	$(QUIET_LD)$(LD) -o $@ $(LDFLAGS) -T bbl/bbl.lds $^

$(O)/%.lds: %.lds.S
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_GEN)$(CPP) -o $@ -P $(CFLAGS) $<

$(O)/%.o: %.S
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC)$(CC) -o $@ -c $(CFLAGS) $<

$(O)/%.o: %.c
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC)$(CC) -o $@ -c $(CFLAGS) -D__MODULE__='"$(basename $(notdir $<))"' $<

$(O)/%.ll: %.c
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC)$(LLVM_CC) -g -o $@ -mno-sse -S -emit-llvm -fno-optimize-sibling-calls -fno-discard-value-names -I include -I../../../klee-2.3/include/klee -I../../../include $(filter-out -g,$(BASE_CFLAGS)) $(CONFIG_CFLAGS) -DCONFIG_VERIFICATION_LLVM -c $<

$(O)/komodo.ll: $(O)/monitor.ll $(O)/traps.ll $(O)/cstate.ll $(O)/specs.ll $(O)/invariants.ll $(O)/libtpot.ll
	$(QUIET_GEN)$(LLVM_LINK) $^ | $(LLVM_OPT) -o $@~ $(LLVM_OPTFLAGS) -S
	$(Q)mv $@~ $@

llvm: $(O)/komodo.ll

$(O)/specs-linked.ll: $(O)/komodo.ll
	cp $< $@

test%: llvm
	../../klee-2.3/build/bin/klee \
	-emit-all-errors --use-independent-solver=false --search=dfs --use-cex-cache=false --use-branch-cache=false \
	--debug-print-instructions=all:stderr --debug-z3-dump-queries=./debug.smt2 --use-constant-arrays=false \
	--use-z3-cache=./z3_cache --entry-point=spec_$@ $(O)/komodo.ll

mrproper: clean
	-rm -f local.mk

distclean: mrproper
	-find . \
		\( -name '*.pyc' -o -name '.DS_Store' \
		-o -name '*.bak' -o -name '*~' \
		-o -name '*.orig' \) \
		-type f -print0 | xargs -0 rm -f
	-find . \
		\( -name '__pycache__' \) \
		-type d -print0 | xargs -0 rm -rf

POTS += spec_kom_smc_map_insecure
POTS += spec_kom_smc_map_secure_fail
POTS += spec_kom_smc_init_l3ptable_fail
POTS += spec_kom_smc_init_l3ptable_success
POTS += spec_kom_smc_init_l2ptable
POTS += spec_kom_smc_init_addrspace
POTS += spec_kom_smc_init_dispatcher
POTS += spec_kom_smc_enter
POTS += spec_kom_smc_resume
POTS += spec_kom_handle_trap
POTS += spec_kom_svc_exit
POTS += spec_kom_smc_stop
POTS += spec_kom_smc_finalise
POTS += spec_kom_smc_remove_addrspace
POTS += spec_kom_smc_remove_else
POTS += spec_kom_smc_map_secure_success

TARGET_SYSTEM = komodo-star

include ../../../Makefile.common

verify_%: $(O)/specs-linked.ll $(KLEE_EXC)
	$(KLEE_EXC) $(KLEE_FLAGS) --check-branch-both-int-bv --entry-point=$(patsubst verify_%,%,$@) $(O)/specs-linked.ll

debug_%: $(O)/specs-linked.ll $(KLEE_EXC)
	gdb --args $(KLEE_EXC) $(KLEE_FLAGS) $(KLEE_DEBUG_FLAGS) --check-branch-both-int-bv --entry-point=$(patsubst debug_%,%,$@) $(O)/specs-linked.ll

verify_spec_kom_smc_map_secure_success: $(O)/specs-linked.ll $(KLEE_EXC)
	$(KLEE_EXC) $(KLEE_FLAGS) --check-branch-both-int-bv --entry-point=spec_kom_smc_map_secure_success $(O)/specs-linked.ll

verify_spec_kom_smc_init_l3ptable_success: $(O)/specs-linked.ll $(KLEE_EXC)
	$(KLEE_EXC) $(KLEE_FLAGS) --check-branch-both-int-bv --entry-point=spec_kom_smc_init_l3ptable_success $(O)/specs-linked.ll

verify_spec_kom_smc_init_l2ptable: $(O)/specs-linked.ll $(KLEE_EXC)
	$(KLEE_EXC) $(KLEE_FLAGS) --check-branch-both-int-bv --entry-point=spec_kom_smc_init_l2ptable $(O)/specs-linked.ll

verify_spec_kom_smc_map_secure_success: $(O)/specs-linked.ll $(KLEE_EXC)
	$(KLEE_EXC) $(KLEE_FLAGS) --check-branch-both-int-bv --entry-point=spec_kom_smc_map_secure_success $(O)/specs-linked.ll

debug_spec_kom_smc_map_secure_success: $(O)/specs-linked.ll $(KLEE_EXC)
	gdb --args $(KLEE_EXC) $(KLEE_FLAGS) --check-branch-both-int-bv --entry-point=spec_kom_smc_map_secure_success $(O)/specs-linked.ll

debug_spec_kom_smc_init_l2ptable: $(O)/specs-linked.ll $(KLEE_EXC)
	gdb --args $(KLEE_EXC) $(KLEE_FLAGS) --check-branch-both-int-bv --entry-point=spec_kom_smc_init_l2ptable $(O)/specs-linked.ll


-include $(call rwildcard,./,*.d)

PHONY           += all clean mrproper distclean

PRECIOUS        += %.asm %.map %.bin %.bin.o $(O)/%.o

.PHONY: $(PHONY)

.PRECIOUS: $(PRECIOUS)
