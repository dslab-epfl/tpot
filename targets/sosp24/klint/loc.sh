# printf "%-15s %-20s %-10s %-10s %-10s %-10s %-10s %-15s %-10s %-20s %-10s %-10s\n" "Component" "Specifications" "Internal" "Predicates" "Proof" "Loops" "Globals" "Linux Models" "Total" "Syntax-only" "Total%" "Proof-to-code%"

CODE=$(cloc env/src/structs/index_pool.c | grep C | awk '{print $5}')

# Verifast
# We use a copy (verifast_index_pool_annotated), since the original file is counted for TPot annotations.
VERIFAST_COUNT_FILES="tpot-specs/index_pool/verifast_index_pool_annotated.c"

VERIFAST_SPECIFICATIONS=$(grep -E 'SPEC' $VERIFAST_COUNT_FILES | wc -l)
VERIFAST_INTERNAL=$(grep -E -- 'INTERNAL' $VERIFAST_COUNT_FILES | wc -l)
VERIFAST_PREDICATES=$(grep -E 'PREDICATE' $VERIFAST_COUNT_FILES | wc -l)
VERIFAST_PROOF=$(grep -E 'PROOF' $VERIFAST_COUNT_FILES | wc -l)
VERIFAST_LOOPS=$(grep -E 'LOOP' $VERIFAST_COUNT_FILES | wc -l)
VERIFAST_GLOBALS=$(grep -E 'GLOBAL' $VERIFAST_COUNT_FILES | wc -l)
VERIFAST_LINUX_MODELS=$(grep -E 'LINUX_MODELS' $VERIFAST_COUNT_FILES | wc -l)

VERIFAST_TOTAL=$((VERIFAST_SPECIFICATIONS + VERIFAST_INTERNAL + VERIFAST_PREDICATES + VERIFAST_PROOF + VERIFAST_LOOPS + VERIFAST_GLOBALS + VERIFAST_LINUX_MODELS))

# count lines that match exactly "include", "return", "{", or "}"
VERIFAST_SYNTAX=$(grep -E 'SYNTAX' $VERIFAST_COUNT_FILES | wc -l)

printf "%-15s %-20s %-10s %-10s %-10s %-10s %-10s %-15s %-10s %-20s %-10s %-10s\n" "Verifast" "$VERIFAST_SPECIFICATIONS" "$VERIFAST_INTERNAL" "$VERIFAST_PREDICATES" "$VERIFAST_PROOF" "$VERIFAST_LOOPS" "$VERIFAST_GLOBALS" "$VERIFAST_LINUX_MODELS" "$VERIFAST_TOTAL" "$VERIFAST_SYNTAX" "$(echo "scale=2; $VERIFAST_TOTAL * 100 / $CODE" | bc)" "$(echo "scale=2; ($VERIFAST_TOTAL - $VERIFAST_SYNTAX) * 100 / $CODE" | bc)"

# TPOT

TPOT_COUNT_FILES="tpot-specs/index_pool/specs.c tpot-specs/index_pool/spec_helpers.h tpot-specs/index_pool/tpot_models.c env/src/structs/index_pool.c"

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
