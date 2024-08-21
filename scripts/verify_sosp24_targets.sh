#!/usr/bin/bash
DIR=$(dirname $0)

# Suppress output
pushd () {
    command pushd "$@" > /dev/null
}
popd () {
    command popd "$@" > /dev/null
}

TARGETS+="targets/sosp24/pkvm-early-alloc/tpot "
TARGETS+="targets/sosp24/klint/tpot-specs/index_pool "
TARGETS+="targets/sosp24/kvm-pgtable "
TARGETS+="targets/sosp24/usbmouse "
TARGETS+="targets/sosp24/komodo-serval "
TARGETS+="targets/sosp24/komodo-star"


# build all targets, silence build output
for target_dir in $TARGETS; do
    pushd $DIR/../$target_dir
    make &> /dev/null
    popd
done

for target_dir in $TARGETS; do
    pushd $DIR/../$target_dir
    make -s verify-all
    echo ""
    popd
done
