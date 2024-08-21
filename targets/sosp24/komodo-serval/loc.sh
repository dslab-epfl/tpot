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

SERVAL_SPECIFICATIONS=$(cloc verif/llvm.rkt verif/basic.rkt verif/spec.rkt | grep SUM | awk '{print $5}')
SERVAL_INTERNAL=0
SERVAL_PREDICATES=0
SERVAL_PROOF=0
SERVAL_LOOPS=0
# To simplify counting, we omit the lines that are syntax-only from files containing global invariants.
SERVAL_GLOBALS=$(grep -E 'GLOBAL' verif/impl.rkt verif/invariants.rkt | wc -l)
SERVAL_LINUX_MODELS=0

SERVAL_TOTAL=$((SERVAL_SPECIFICATIONS + SERVAL_INTERNAL + SERVAL_PREDICATES + SERVAL_PROOF + SERVAL_LOOPS + SERVAL_GLOBALS + SERVAL_LINUX_MODELS))

# count the lines with/within 'require', '#lang' and parenthesis
SERVAL_SYNTAX=0
for file in verif/llvm.rkt verif/basic.rkt verif/spec.rkt; do
    require_inside=$(awk '/^\(require/ && $0 !~ /\)$/ {inside=1; next} inside && /^\)/ {inside=0; next} inside {print}' $file | wc -l)
    require=$(grep -E "\(require" $file | wc -l)
    lang=$(grep -E "#lang" $file | wc -l)
    parenthesis=$(grep -E "^\s*\(+\s*\)+$|^\s*\)+\s*\(+$|^\s*\(+$|^\s*\)+$" $file | wc -l)
    SERVAL_SYNTAX=$((require_inside + require + lang + parenthesis + SERVAL_SYNTAX))
done

# printf "%-15s %-20s %-10s %-10s %-10s %-10s %-10s %-15s %-10s %-20s %-10s %-10s\n" "Component" "Specifications" "Internal" "Predicates" "Proof" "Loops" "Globals" "Linux Models" "Total" "Syntax-only" "Total%" "Proof-to-code%"
printf "%-15s %-20s %-10s %-10s %-10s %-10s %-10s %-15s %-10s %-20s %-10s %-10s\n" "Serval" "$SERVAL_SPECIFICATIONS" "$SERVAL_INTERNAL" "$SERVAL_PREDICATES" "$SERVAL_PROOF" "$SERVAL_LOOPS" "$SERVAL_GLOBALS" "$SERVAL_LINUX_MODELS" "$SERVAL_TOTAL" "$SERVAL_SYNTAX" "$(echo "scale=2; $SERVAL_TOTAL * 100 / $CODE" | bc)" "$(echo "scale=2; ($SERVAL_TOTAL - $SERVAL_SYNTAX) * 100 / $CODE" | bc)"

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