#!/usr/bin/bash
TPOT_SPECS_DIR=$1
TARGET_POT=$2
TARGET_SYSTEM=$3

TARGET=${TARGET_SYSTEM}__${TARGET_POT}


VERIF_DIR=$(pwd)/${TPOT_SPECS_DIR}/../o.${TARGET}_$(date +%Y%m%d_%H%M%S)

mkdir -p "$(dirname ${VERIF_DIR})"

cp -r ${TPOT_SPECS_DIR} ${VERIF_DIR}
cd ${VERIF_DIR}

if [[ $TARGET_POT == init_* ]]; then
    MAKE_TARGET=verify-init_${TARGET_POT#init_}
else
    MAKE_TARGET=verify_$TARGET_POT
fi

start=$(date +%s)

make $MAKE_TARGET Z3_CACHE=~/z3_cache/${TARGET}.smt2.cache 2> log.txt 
end=$(date +%s)
duration=$((end - start))

# Parse last lines of output to determine verification result
if tail -n 2 log.txt | head -n 1 | grep "failed" > /dev/null; then
    echo "POT $TARGET failed in $duration, see $VERIF_DIR/log.txt"
elif tail -n 2 log.txt | grep "succeeded" > /dev/null; then
    if tail -n 2 log.txt | head -n 1 | grep "but there are memory leaks" > /dev/null; then
        echo "POT $TARGET passed, but found memory leaks in $duration secs"
    else
        echo "POT $TARGET passed in $duration secs"
    fi
else
    echo "POT $TARGET failed in $duration, see $VERIF_DIR/log.txt"
fi
