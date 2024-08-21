CURDIR=`pwd`
ORIG_DIR=../.tmp/pgtable_original

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
# Download the refinedc case study
wget -q https://gitlab.mpi-sws.org/iris/refinedc/-/raw/master/linux/casestudies/pgtable.c
wget -q https://gitlab.mpi-sws.org/iris/refinedc/-/raw/master/linux/casestudies/proofs/pgtable/pgtable_lemmas.v

mkdir relevant_components
cp pgtable.c relevant_components/pgtable.c
cp pgtable_lemmas.v relevant_components/pgtable_lemmas.v

# Comment out refinedC annotations ( [[ ... ]] ), as the C file does not compile with them
perl -0777 -pi -e 's/\[\[.*?\]\]/\/* $& *\//sg' relevant_components/pgtable.c

# # Copy the version verified by TPOT, leaving out TPOT-specific files and scripts
mkdir tpot_target
cp -r $CURDIR/pgtable.c \
      $CURDIR/pgtable_lemmas.v \
      tpot_target

# Remove the markers used to count lines of specs.
perl -pi -e 's/\/\*SPEC\*\/\s//g' tpot_target/pgtable.c
perl -pi -e 's/\/\*SYNTAX\*\/\s//g' tpot_target/pgtable.c
perl -pi -e 's/\/\/SPEC//g' tpot_target/pgtable.c
perl -pi -e 's/\/\*INTERNAL\*\/\s*//g' tpot_target/pgtable.c
perl -pi -e 's/\/\*PROOF\*\/\s*//g' tpot_target/pgtable.c
perl -pi -e 's/\/\*SPEC\*\/\s//g' tpot_target/pgtable_lemmas.v
perl -pi -e 's/\/\*PROOF CONTROL\*\/ //g' tpot_target/pgtable_lemmas.v
perl -pi -e 's/\/\*PROOF\*\/\s*//g' tpot_target/pgtable_lemmas.v
perl -pi -e 's/\/\*SYNTAX\*\/\s//g' tpot_target/pgtable_lemmas.v

# Diff the two directories
diff -r relevant_components tpot_target

popd 