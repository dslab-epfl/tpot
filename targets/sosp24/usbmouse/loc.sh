# printf "%-15s %-20s %-10s %-10s %-10s %-10s %-10s %-15s %-10s %-20s %-10s %-10s\n" "Component" "Specifications" "Internal" "Predicates" "Proof" "Loops" "Globals" "Linux Models" "Total" "Syntax-only" "Total%" "Proof-to-code%"

CODE=$(cloc linux/device.h linux/errno.h linux/gfp.h linux/input.h linux/kernel.h linux/mod_devicetable.h linux/slab_def.h linux/stddef.h linux/string.h linux/types.h linux/usb.h linux/usb/* usbmouse_original.c  | grep SUM | awk '{print $5}')

# Verifast
VERIFAST_COUNT_FILES="usbmouse_verifast.c linux/mod_devicetable.h linux/usb.h linux/input.h"

VERIFAST_SPECIFICATIONS=$(grep -E 'SPEC' $VERIFAST_COUNT_FILES | wc -l)
VERIFAST_INTERNAL=$(grep -E 'INTERNAL' $VERIFAST_COUNT_FILES | wc -l)
VERIFAST_PREDICATES=$(grep -E 'PREDICATE' $VERIFAST_COUNT_FILES | wc -l)
VERIFAST_PROOF=$(grep -E 'PROOF' $VERIFAST_COUNT_FILES | wc -l)
VERIFAST_LOOPS=0
VERIFAST_GLOBALS=0
VERIFAST_LINUX_MODELS=0

VERIFAST_TOTAL=$((VERIFAST_SPECIFICATIONS + VERIFAST_INTERNAL + VERIFAST_PREDICATES + VERIFAST_PROOF + VERIFAST_LOOPS + VERIFAST_GLOBALS + VERIFAST_LINUX_MODELS))

VERIFAST_SYNTAX=$(grep -E 'SYNTAX' $VERIFAST_COUNT_FILES | wc -l) # TODO

printf "%-15s %-20s %-10s %-10s %-10s %-10s %-10s %-15s %-10s %-20s %-10s %-10s\n" "Verifast" "$VERIFAST_SPECIFICATIONS" "$VERIFAST_INTERNAL" "$VERIFAST_PREDICATES" "$VERIFAST_PROOF" "$VERIFAST_LOOPS" "$VERIFAST_GLOBALS" "$VERIFAST_LINUX_MODELS" "$VERIFAST_TOTAL" "$VERIFAST_SYNTAX" "$(echo "scale=2; $VERIFAST_TOTAL * 100 / $CODE" | bc)" "$(echo "scale=2; ($VERIFAST_TOTAL - $VERIFAST_SYNTAX) * 100 / $CODE" | bc)"

# TPOT

TPOT_COUNT_FILES="usbmouse_tpot.c specs.c spec_helpers.c spec_helpers.h linux_tpot.c"

TPOT_SPECIFICATIONS=$(grep -E 'SPECS' $TPOT_COUNT_FILES | wc -l)
TPOT_INTERNAL=$(grep -E -- 'INTERNAL' $TPOT_COUNT_FILES | wc -l)
TPOT_PREDICATES=$(grep -E 'PREDICATES' $TPOT_COUNT_FILES | wc -l)
TPOT_PROOF=$(grep -E 'PROOF' $TPOT_COUNT_FILES | wc -l)
TPOT_LOOPS=$(grep -E 'LOOPINV' $TPOT_COUNT_FILES | wc -l)
TPOT_GLOBALS=$(grep -E 'GLOBAL' $TPOT_COUNT_FILES | wc -l)
TPOT_LINUX_MODELS=$(cloc linux_tpot.c | grep C | awk '{print $5}')

TPOT_TOTAL=$((TPOT_SPECIFICATIONS + TPOT_INTERNAL + TPOT_PREDICATES + TPOT_PROOF + TPOT_LOOPS + TPOT_GLOBALS + TPOT_LINUX_MODELS))

TPOT_SYNTAX=$(grep -E 'SYNTAX' $TPOT_COUNT_FILES | wc -l)

printf "%-15s %-20s %-10s %-10s %-10s %-10s %-10s %-15s %-10s %-20s %-10s %-10s\n" "TPot" "$TPOT_SPECIFICATIONS" "$TPOT_INTERNAL" "$TPOT_PREDICATES" "$TPOT_PROOF" "$TPOT_LOOPS" "$TPOT_GLOBALS" "$TPOT_LINUX_MODELS" "$TPOT_TOTAL" "$TPOT_SYNTAX" "$(echo "scale=2; $TPOT_TOTAL * 100 / $CODE" | bc)" "$(echo "scale=2; ($TPOT_TOTAL - $TPOT_SYNTAX) * 100 / $CODE" | bc)"
