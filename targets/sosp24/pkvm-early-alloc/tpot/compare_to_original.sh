CURDIR=`pwd`
ORIG_DIR=../.tmp/early_alloc_original

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
# Download the CN case study
wget -q https://github.com/rems-project/CN-pKVM-early-allocator-case-study/archive/refs/heads/main.zip
unzip -q main.zip

mkdir relevant_components
cp -r CN-pKVM-early-allocator-case-study-main/verifast \
      CN-pKVM-early-allocator-case-study-main/cn \
      CN-pKVM-early-allocator-case-study-main/original \
      relevant_components

# # Copy the version verified by TPOT, leaving out TPOT-specific files and scripts
mkdir tpot_target
cp -r $CURDIR/../verifast \
      $CURDIR/../cn \
      $CURDIR/../original \
      tpot_target
# Remove the markers used to count lines of specs.
perl -pi -e 's/\/\*GLOBAL\*\/\s//g' tpot_target/cn/cn_predicates.h
perl -pi -e 's/\/\*SYNTAX\*\/\s//g' tpot_target/cn/cn_predicates.h
perl -pi -e 's/\/\*PREDICATES\*\/\s//g' tpot_target/cn/early_alloc.c
perl -pi -e 's/\/\*SPECS\*\/\s//g' tpot_target/cn/early_alloc.c
perl -pi -e 's/\/\*LOOPINV\*\/\s//g' tpot_target/cn/early_alloc.c
perl -pi -e 's/\/\*INTERNAL\*\/\s//g' tpot_target/cn/early_alloc.c
perl -pi -e 's/\/\*PREDICATES\*\/\s//g' tpot_target/cn/memory.h
perl -pi -e 's/\/\*SPECS\*\/\s//g' tpot_target/cn/memory.h
perl -pi -e 's/\/\*INTERNAL\*\/\s//g' tpot_target/cn/memory.h

perl -pi -e 's/\/\*SPEC\*\///g'  relevant_components/verifast/early_alloc.c
perl -pi -e 's/\/\*SPEC\*\///g' relevant_components/verifast/memory.h
perl -pi -e 's/\/\*SPECS\*\/ //g' tpot_target/verifast/early_alloc.c
perl -pi -e 's/\/\*LOOPINV\*\///g' tpot_target/verifast/early_alloc.c
perl -pi -e 's/\/\*INTERNAL\*\/\s//g' tpot_target/verifast/early_alloc.c
perl -pi -e 's/\/\*PREDICATES\*\/\s//g' tpot_target/verifast/early_alloc.c
perl -pi -e 's/\/\*PROOF\*\///g' tpot_target/verifast/early_alloc.c
perl -pi -e 's/\/\*PROOF\*\/ //g' tpot_target/verifast/lemmas.h
perl -pi -e 's/\/\*SPECS\*\///g' tpot_target/verifast/memory.h
perl -pi -e 's/\/\*INTERNAL\*\///g' tpot_target/verifast/memory.h
perl -pi -e 's/\/\*GLOBAL\*\/ //g' tpot_target/verifast/verifast_predicates.h
perl -pi -e 's/\/\*SPECS\*\/\s//g' tpot_target/verifast/verifast_predicates.h
perl -pi -e 's/\/\*SYNTAX\*\/\s//g' tpot_target/verifast/verifast_predicates.h

perl -pi -e 's/\/\* LOOPINV\*\/ //g'  tpot_target/original/early_alloc.c
perl -pi -e 's/\/\*LOOPINV\*\///g'  tpot_target/original/early_alloc.c
perl -pi -e 's/\/\*SYNTAX\*\/\s*//g' tpot_target/original/early_alloc.c

# # Diff the two directories
diff -r relevant_components tpot_target

popd 