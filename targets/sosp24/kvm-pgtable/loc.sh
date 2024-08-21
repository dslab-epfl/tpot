# printf "%-15s %-20s %-10s %-10s %-10s %-10s %-10s %-15s %-10s %-20s %-10s %-10s\n" "Component" "Specifications" "Internal" "Predicates" "Proof" "Loops" "Globals" "Linux Models" "Total" "Syntax-only" "Total%" "Proof-to-code%"

CODE=$(cloc pgtable.c | grep C | awk '{print $5}')

# RefinedC

REFINEDC_COUNT_FILES="pgtable.c pgtable_lemmas.v"

REFINEDC_SPECIFICATIONS=$(grep -E 'SPEC' $REFINEDC_COUNT_FILES | wc -l)
REFINEDC_INTERNAL=$(grep -E -- 'INTERNAL' $REFINEDC_COUNT_FILES | wc -l)
REFINEDC_PREDICATES=$(grep -E 'RC_PRED' $REFINEDC_COUNT_FILES | wc -l)
REFINEDC_PROOF=$(grep -E 'PROOF' $REFINEDC_COUNT_FILES | wc -l)
REFINEDC_LOOPS=$(grep -E 'LOOP' $REFINEDC_COUNT_FILES | wc -l)
REFINEDC_GLOBALS=$(grep -E 'RC_GLOBAL' $REFINEDC_COUNT_FILES | wc -l)
REFINEDC_LINUX_MODELS=$(grep -E 'RC_LINUX_MODELS' $REFINEDC_COUNT_FILES | wc -l)

REFINEDC_TOTAL=$((REFINEDC_SPECIFICATIONS + REFINEDC_INTERNAL + REFINEDC_PREDICATES + REFINEDC_PROOF + REFINEDC_LOOPS + REFINEDC_GLOBALS + REFINEDC_LINUX_MODELS))

# count lines that match exactly "include", "return", "{", or "}"
REFINEDC_SYNTAX=$(grep -E 'SYNTAX' $REFINEDC_COUNT_FILES | wc -l)

printf "%-15s %-20s %-10s %-10s %-10s %-10s %-10s %-15s %-10s %-20s %-10s %-10s\n" "RefinedC" "$REFINEDC_SPECIFICATIONS" "$REFINEDC_INTERNAL" "$REFINEDC_PREDICATES" "$REFINEDC_PROOF" "$REFINEDC_LOOPS" "$REFINEDC_GLOBALS" "$REFINEDC_LINUX_MODELS" "$REFINEDC_TOTAL" "$REFINEDC_SYNTAX" "$(echo "scale=2; $REFINEDC_TOTAL * 100 / $CODE" | bc)" "$(echo "scale=2; ($REFINEDC_TOTAL - $REFINEDC_SYNTAX) * 100 / $CODE" | bc)"

# TPOT

TPOT_COUNT_FILES="specs.c"

TPOT_SPECIFICATIONS=$(grep -E 'SPECS' $TPOT_COUNT_FILES | wc -l)
TPOT_INTERNAL=$(grep -E -- 'INTERNAL' $TPOT_COUNT_FILES | wc -l)
TPOT_PREDICATES=$(grep -E 'PREDICATES' $TPOT_COUNT_FILES | wc -l)
TPOT_PROOF=$(grep -E 'PROOF' $TPOT_COUNT_FILES | wc -l)
TPOT_LOOPS=$(grep -E 'LOOPINV' $TPOT_COUNT_FILES | wc -l)
TPOT_GLOBALS=$(grep -E 'GLOBAL' $TPOT_COUNT_FILES | wc -l)
TPOT_LINUX_MODELS=$(grep -E 'LINUX_MODELS' $TPOT_COUNT_FILES | wc -l)

TPOT_TOTAL=$((TPOT_SPECIFICATIONS + TPOT_INTERNAL + TPOT_PREDICATES + TPOT_PROOF + TPOT_LOOPS + TPOT_GLOBALS + TPOT_LINUX_MODELS))

# count lines that match exactly "include", "return", "{", or "}"
TPOT_SYNTAX=$(grep -E 'SYNTAX' $TPOT_COUNT_FILES | wc -l)

printf "%-15s %-20s %-10s %-10s %-10s %-10s %-10s %-15s %-10s %-20s %-10s %-10s\n" "TPot" "$TPOT_SPECIFICATIONS" "$TPOT_INTERNAL" "$TPOT_PREDICATES" "$TPOT_PROOF" "$TPOT_LOOPS" "$TPOT_GLOBALS" "$TPOT_LINUX_MODELS" "$TPOT_TOTAL" "$TPOT_SYNTAX" "$(echo "scale=2; $TPOT_TOTAL * 100 / $CODE" | bc)" "$(echo "scale=2; ($TPOT_TOTAL - $TPOT_SYNTAX) * 100 / $CODE" | bc)"
