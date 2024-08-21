TMPFILE=$TMPDIR/count.csv



# count lines of code
CODE_TOTAL=$(cloc --hide-rate --quiet --sum-one -csv original | awk 'END{print}' | awk -F "," '{print $NF}')
echo "Code,total,${CODE_TOTAL}" > $TMPFILE


# CN

CN_SPEC=$(grep -E -- '\/\*@' cn/early_alloc.c cn/memory.h | wc -l | tr -d ' ' | awk -F "," '{print $NF}')
echo "CN,specification,${CN_SPEC}" >> $TMPFILE

CN_INSTR=$(grep -E -- '\/\*CN\*\/' cn/early_alloc.c cn/memory.h | wc -l | tr -d ' ' | awk -F "," '{print $NF}')
echo "CN,instrumentation,${CN_INSTR}" >> $TMPFILE

CN_DEF=$(cloc --hide-rate --quiet --sum-one -csv cn/cn_predicates.h | awk 'END{print}' | awk -F "," '{print $NF}')
echo "CN,definition,${CN_DEF}" >> $TMPFILE

CN_TOTAL=$((CN_SPEC + CN_INSTR + CN_DEF))
echo "CN,total,${CN_TOTAL}" >> $TMPFILE

CN_OVERHEAD=$( echo "$CN_TOTAL / $CODE_TOTAL" | bc -l )
echo "CN,overhead,${CN_OVERHEAD}" >> $TMPFILE


# Frama-C

FRAMAC_SPEC=$(grep -E -- 'requires|ensures|assigns|invariant' frama-c/early_alloc.c frama-c/memory.h | wc -l | tr -d ' ' | awk -F "," '{print $NF}')
echo "Frama-C,specification,${FRAMAC_SPEC}" >> $TMPFILE

FRAMAC_OVERHEAD=$( echo "$FRAMAC_SPEC / $CODE_TOTAL" | bc -l )
echo "Frama-C,overhead,${FRAMAC_OVERHEAD}" >> $TMPFILE


# RefinedC

REFINEDC_SKIPPED_CODE=$(grep -r -E -- 'RCIGNORE' original | wc -l  | tr -d ' ' | awk -F "," '{print $NF}')
echo "RefinedC,skipped code size,${REFINEDC_SKIPPED_CODE}" >> $TMPFILE
REFINEDC_VERIFIED_CODE=$(($CODE_TOTAL - $REFINEDC_SKIPPED_CODE))
echo "RefinedC,verified code size,${REFINEDC_VERIFIED_CODE}" >> $TMPFILE

REFINEDC_TOTAL_SPEC=$(grep -E -- '\[\[rc' refinedc/early_alloc.c refinedc/memory.h | wc -l | tr -d ' ' | awk -F "," '{print $NF}')
echo "RefinedC,specification (including ignored parts),${REFINEDC_TOTAL_SPEC}" >> $TMPFILE

REFINEDC_IGNORED_SPEC=$(grep -E -- 'RCSPECIGNORE' refinedc/early_alloc.c refinedc/memory.h | wc -l | tr -d ' ' | awk -F "," '{print $NF}')
echo "RefinedC,ignored specification,${REFINEDC_IGNORED_SPEC}" >> $TMPFILE

REFINEDC_SPEC=$(($REFINEDC_TOTAL_SPEC-$REFINEDC_IGNORED_SPEC))
echo "RefinedC,specification (without ignored parts),${REFINEDC_SPEC}" >> $TMPFILE

REFINEDC_INSTR=$(grep -E -- '\/\*REFINEDC\*\/' refinedc/early_alloc.c refinedc/memory.h | wc -l | tr -d ' ' | awk -F "," '{print $NF}')
echo "RefinedC,instrumentation,${REFINEDC_INSTR}" >> $TMPFILE

REFINEDC_DEF=$(grep -E -- '\/\/@\ ' refinedc/definitions.h | wc -l | tr -d ' ' | awk -F "," '{print $NF}')
echo "RefinedC,definition,${REFINEDC_DEF}" >> $TMPFILE

REFINEDC_PROOF=$(grep -E -- '\/\/@\ ' refinedc/proofs.h | wc -l | tr -d ' ' | awk -F "," '{print $NF}')
echo "RefinedC,proof,${REFINEDC_PROOF}" >> $TMPFILE

REFINEDC_TOTAL=$((REFINEDC_SPEC + REFINEDC_INSTR + REFINEDC_DEF + REFINEDC_PROOF))
echo "RefinedC,total (without ignored parts),${REFINEDC_TOTAL}" >> $TMPFILE

REFINEDC_OVERHEAD=$( echo "$REFINEDC_TOTAL / $REFINEDC_VERIFIED_CODE" | bc -l )
echo "RefinedC,overhead (without skipped parts),${REFINEDC_OVERHEAD}" >> $TMPFILE


# VeriFast

VERIFAST_SPEC=$(grep -E -- '\/\*SPEC\*\/' verifast/early_alloc.c verifast/memory.h | wc -l | tr -d ' ' | awk -F "," '{print $NF}')
echo "VeriFast,specification,${VERIFAST_SPEC}" >> $TMPFILE

VERIFAST_INSTR=$(grep -E -- '\/\*VERIFAST\*\/' verifast/early_alloc.c verifast/memory.h | wc -l | tr -d ' ' | awk -F "," '{print $NF}')
echo "VeriFast,instrumentation,${VERIFAST_INSTR}" >> $TMPFILE

VERIFAST_DEF=$(cloc --hide-rate --quiet --sum-one -csv verifast/verifast_predicates.h | awk 'END{print}' | awk -F "," '{print $(NF-1)}')
echo "VeriFast,definition,${VERIFAST_DEF}" >> $TMPFILE

VERIFAST_LEMMA=$(cloc --hide-rate --quiet --sum-one -csv verifast/lemmas.h | awk 'END{print}' | awk -F "," '{print $(NF-1)}')
echo "VeriFast,lemma,${VERIFAST_LEMMA}" >> $TMPFILE

VERIFAST_TOTAL=$((VERIFAST_SPEC + VERIFAST_INSTR + VERIFAST_DEF + VERIFAST_LEMMA))
echo "VeriFast,total,${VERIFAST_TOTAL}" >> $TMPFILE

VERIFAST_OVERHEAD=$( echo "$VERIFAST_TOTAL / $CODE_TOTAL" | bc -l )
echo "VeriFast,overhead,${VERIFAST_OVERHEAD}" >> $TMPFILE



column -t -s, $TMPFILE
