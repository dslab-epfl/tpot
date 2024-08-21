#!/usr/bin/bash
TPOT_SPECS_DIR=$1
TARGET_SYSTEM=$2
POTS=$3

DIR=$(dirname $0)

ALL_ARGS=( ${@} )
TARGETS="${ALL_ARGS[*]:2}"

NUM_TARGETS=$(echo "$TARGETS" | wc -w)
echo "Running $NUM_TARGETS POTs in parallel for $TARGET_SYSTEM"

for target in $TARGETS; do
    $DIR/run_pot.sh $TPOT_SPECS_DIR $target $TARGET_SYSTEM &
done

wait
echo "--- All POTs done for $TARGET_SYSTEM ! ---"
