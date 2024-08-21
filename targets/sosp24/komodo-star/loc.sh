CODE=$(cloc monitor.c monitor.h csrs.h cstate.c \
    include/asm/csr.h \
    include/asm/pmp.h \
    include/asm/entry.h \
    include/asm/pgtable.h \
    include/asm/ptrace.h \
    include/asm/page.h \
    include/io/compiler.h \
    include/io/const.h \
    include/io/sizes.h \
    include/io/linkage.h \
    include/io/build_bug.h \
    include/asm/tlbflush.h \
    include/asm/csr_bits/status.h \
    include/asm/setup.h \
    include/sys/errno.h \
    include/sys/types.h \
    include/sys/init.h \
    include/sys/string.h \
    include/sys/bug.h | grep SUM | awk '{print $5}')

# printf "%-15s %-20s %-10s %-10s %-10s %-10s %-10s %-15s %-10s %-20s %-10s %-10s\n" "Component" "Specifications" "Internal" "Predicates" "Proof" "Loops" "Globals" "Linux Models" "Total" "Syntax-only" "Total%" "Proof-to-code%"

TPOT_SPECS=$(cloc specs.c | grep C | awk '{print $5}')
TPOT_INTERNAL=0
TPOT_PREDICATES=0
TPOT_PROOF=0
TPOT_LOOPS=0
TPOT_GLOBALS=$(cloc invariants.c | grep C | awk '{print $5}')
TPOT_LINUX_MODELS=0

TPOT_TOTAL=$((TPOT_SPECS + TPOT_INTERNAL + TPOT_PREDICATES + TPOT_PROOF + TPOT_LOOPS + TPOT_GLOBALS + TPOT_LINUX_MODELS))

# count lines that match exactly "include", "return", "{", or "}"
TPOT_SYNTAX=0
for file in specs.c invariants.c; do
    count=$(grep -Ecx '^\s*(#include.*|return;|{|})\s*$' "$file")
    # Add to total count
    TPOT_SYNTAX=$((TPOT_SYNTAX + count))
done

printf "%-15s %-20s %-10s %-10s %-10s %-10s %-10s %-15s %-10s %-20s %-10s %-10s\n" "TPot" "$TPOT_SPECS" "$TPOT_INTERNAL" "$TPOT_PREDICATES" "$TPOT_PROOF" "$TPOT_LOOPS" "$TPOT_GLOBALS" "$TPOT_LINUX_MODELS" "$TPOT_TOTAL" "$TPOT_SYNTAX" "$(echo "scale=2; $TPOT_TOTAL * 100 / $CODE" | bc)" "$(echo "scale=2; ($TPOT_TOTAL - $TPOT_SYNTAX) * 100 / $CODE" | bc)"