CURDIR=`pwd`
ORIG_DIR=../.tmp/kom_tpot_original

# Suppress output
pushd () {
    command pushd "$@" > /dev/null
}
popd () {
    command popd "$@" > /dev/null
}

rm -rf $ORIG_DIR
mkdir -p $ORIG_DIR

pushd $ORIG_DIR

# Copy relevant files from komodo-serval
mkdir relevant_components
cp -r $CURDIR/../komodo-serval/bbl \
      $CURDIR/../komodo-serval/bios \
      $CURDIR/../komodo-serval/include \
      $CURDIR/../komodo-serval/kernel \
      $CURDIR/../komodo-serval/komodo-kernel \
      $CURDIR/../komodo-serval/verif \
      $CURDIR/../komodo-serval/csrs.h $CURDIR/../komodo-serval/komodo.mk $CURDIR/../komodo-serval/main.c $CURDIR/../komodo-serval/config.mk \
      $CURDIR/../komodo-serval/monitor.c $CURDIR/../komodo-serval/monitor.h $CURDIR/../komodo-serval/traps.c \
      $CURDIR/../komodo-serval/include/asm/cstate.h \
      $CURDIR/../komodo-serval/specs.c $CURDIR/../komodo-serval/invariants.c \
      relevant_components

# Copy komodo-star files.
mkdir tpot_target
cp -r $CURDIR/bbl \
      $CURDIR/bios \
      $CURDIR/include \
      $CURDIR/kernel \
      $CURDIR/komodo-kernel \
      $CURDIR/verif \
      $CURDIR/csrs.h $CURDIR/komodo.mk $CURDIR/main.c $CURDIR/config.mk \
      $CURDIR/monitor.c $CURDIR/monitor.h $CURDIR/traps.c \
      $CURDIR/include/asm/cstate.h \
      $CURDIR/specs.c $CURDIR/invariants.c \
      tpot_target

# Diff the two directories
diff -r relevant_components tpot_target

popd