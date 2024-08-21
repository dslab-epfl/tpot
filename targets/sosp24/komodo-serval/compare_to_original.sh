CURDIR=`pwd`
ORIG_DIR=../.tmp/kom_serval_original

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
# Download the serval code
wget -q https://github.com/uw-unsat/serval-sosp19/archive/refs/heads/master.zip
unzip -q master.zip

# Extract the relevant components
mkdir relevant_components
cp -r serval-sosp19-master/monitors/komodo/* \
      serval-sosp19-master/bios \
      serval-sosp19-master/include \
      serval-sosp19-master/kernel \
      serval-sosp19-master/config.mk \
      relevant_components
# move the relevant kernel files to komodo-kernel
mkdir relevant_components/komodo-kernel; cp serval-sosp19-master/monitors/komodo/kernel/kernel.mk relevant_components/komodo-kernel/kernel.mk
mv relevant_components/kernel/main.c relevant_components/kernel/smc.S relevant_components/kernel/test.S relevant_components/komodo-kernel

mkdir relevant_components/bbl; cp serval-sosp19-master/bbl/payload.S relevant_components/bbl/payload.S
rm relevant_components/verif/generated


# Copy the version verified by TPOT, leaving out TPOT-specific files and scripts
mkdir tpot_target
cp -r $CURDIR/bbl \
      $CURDIR/bios \
      $CURDIR/include \
      $CURDIR/kernel \
      $CURDIR/komodo-kernel \
      $CURDIR/verif \
      $CURDIR/csrs.h $CURDIR/komodo.mk $CURDIR/main.c $CURDIR/config.mk \
      $CURDIR/monitor.c $CURDIR/monitor.h $CURDIR/traps.c \
      tpot_target

# This defines C models for assembly code, and is not originally a part of Komodo.
# (see comments in include/asm/csr.h)
rm tpot_target/include/asm/cstate.h  

# Remove the markers used to count lines of specs.
perl -pi -e 's/\/\*GLOBAL\*\/ //g' tpot_target/verif/invariants.rkt
perl -pi -e 's/\/\*GLOBAL\*\/ //g' tpot_target/verif/impl.rkt

# Diff the two directories
diff -r relevant_components tpot_target

popd 