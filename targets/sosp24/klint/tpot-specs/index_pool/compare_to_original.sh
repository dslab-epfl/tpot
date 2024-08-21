CURDIR=`pwd`
ORIG_DIR=../.tmp/klint_original

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
# Download the Klint code, which includes Vigor data structures.
wget -q https://github.com/dslab-epfl/klint/archive/refs/heads/main.zip
unzip -q main.zip

# Extract the relevant components
mkdir -p relevant_components/env
cp -r klint-main/env/include \
      klint-main/env/src \
      relevant_components/env
# We only care about the index pool struct
rm relevant_components/env/include/structs/*
rm relevant_components/env/src/structs/*
cp klint-main/env/include/structs/index_pool.h \
   relevant_components/env/include/structs/index_pool.h
cp klint-main/env/src/structs/index_pool.c \
   relevant_components/env/src/structs/index_pool.c
# This is not used
rm -rf relevant_components/env/src/net



# # Copy the version verified by TPOT, leaving out TPOT-specific files and scripts
mkdir tpot_target
cp -r $CURDIR/../../env \
      tpot_target
# Remove the markers used to count lines of specs.
perl -pi -e 's/\/\*LOOPINV\*\/\s//g' tpot_target/env/src/structs/index_pool.c
perl -pi -e 's/\/\*SYNTAX\*\///g' tpot_target/env/src/structs/index_pool.c

# Diff the two directories
diff -r relevant_components tpot_target

popd 