#!/bin/bash

# Where to put the portfolio
PORTFOLIO_PATH=$1
# pass either a known portfolio name (sosp24, minimal)
PORTFOLIO_NAME=${2:-"minimal"}

DIR=$(dirname $0)

# set -e

# ----------------
# Helper funcitons
# ----------------

# We don't use this in CI since it takes longer. We donwload the binaries instead. 
build_z3_versions() {
    for VERSION in "$@"
    do
            wget https://github.com/Z3Prover/z3/archive/refs/tags/z3-$VERSION.tar.gz > /dev/null
            tar -xf z3-$VERSION.tar.gz > /dev/null
            cd z3-z3-$VERSION || exit
            python scripts/mk_make.py > /dev/null
            cd build || exit
            make -j48 > /dev/null
            cd  ../..
            echo "Finished building Z3 $VERSION"
    done
}

download_z3_binary() {
    version=$1
    url=https://github.com/Z3Prover/z3/releases/download/z3-$version/z3-$version-x64-glibc-2.31.zip

    # These versions have non-standard URLs
    if [ $version == "4.8.1" ]; then
        url=https://github.com/Z3Prover/z3/releases/download/z3-4.8.1/z3-4.8.1.b301a59899ff-x86-ubuntu-14.04.zip
        https://github.com/Z3Prover/z3/releases/download/z3-4.8.10/z3-4.8.10-x64-ubuntu-18.04.zip
    fi

    echo "Trying to download $url"

    wget -q -O z3-$version.zip $url
    if [ $? -ne 0 ]; then
        url=https://github.com/Z3Prover/z3/releases/download/z3-$version/z3-$version-x64-glibc-2.31.zip
        echo "Failed. Trying $url"
        wget -q -O z3-$version.zip  $url
        if [ $? -ne 0 ]; then
            url=https://github.com/Z3Prover/z3/releases/download/z3-$version/z3-$version-x64-ubuntu-18.04.zip
            echo "Failed. Trying $url"
            wget -q -O z3-$version.zip  $url
            if [ $? -ne 0 ]; then
                url=https://github.com/Z3Prover/z3/releases/download/z3-$version/z3-$version-x64-ubuntu-14.04.zip
                echo "Failed. Trying $url"
                wget -q -O z3-$version.zip  $url
                if [ $? -ne 0 ]; then
                    echo "Could not download Z3 $version"
                    exit 1
                fi
            fi
        fi
    fi

    unzip -q -o z3-$version.zip
    rm z3-$version.zip
}

setup_configured_solver() {
    original_solver=$1
    configuration=$2
    name=$3

    curdir=$(pwd)


    mkdir -p $curdir/$name/bin
    echo '#!/bin/bash

    DIR=$(dirname $0)

    CONF="'$configuration'"

    $DIR/../../'$original_solver'/bin/z3 $CONF $1' > $curdir/$name/bin/z3

    chmod +x $curdir/$name/bin/z3
}

setup_sosp24() {
    pushd $1

    # Set up unconfigured solvers
    for VERSION in 4.10.2  4.11.2  4.12.5  4.8.10  4.8.17  4.9.0  4.11.0  4.12.2  4.4.1  4.8.12  4.9.1
    # for VERSION in 4.10.2  4.11.2  4.12.5  4.8.10  4.8.17  4.9.0  4.10.0  4.11.0  4.12.2  4.4.1  4.8.12  4.8.1  4.9.1
    # for VERSION in 4.11.2 4.12.6 4.13.0 4.4.1 4.8.1 4.9.1
    do
        download_z3_binary $VERSION
    done

    # Set up configured solvers
    setup_configured_solver z3-4.12.2-x64-glibc-2.31 'smt.arith.branch_cut_ratio=1024 smt.arith.solver=5 smt.threads=24' configured-z3-4.12.2

    popd
}

setup_minimal () {
    pushd $1

    download_z3_binary 4.12.2
    setup_configured_solver z3-4.12.2-x64-glibc-2.31 'smt.relevancy=0' configured-z3-4.12.2

    popd
}

# -----------
# Main script
# -----------

echo "Setting up portfolio $PORTFOLIO_NAME at $PORTFOLIO_PATH"

if [ $PORTFOLIO_NAME != "sosp24" ] && [ $PORTFOLIO_NAME != "minimal" ]; then
  echo "Unknown portfolio name: $PORTFOLIO"
  exit 1
fi

# Create the portfolio directory
mkdir -p $PORTFOLIO_PATH
# Check if mkdir failed
if [ $? -ne 0 ]; then
    echo "Failed to create portfolio directory"
    exit 1
fi

cp $DIR/run-portfolio.sh $PORTFOLIO_PATH
cp $DIR/run-portfolio-all.sh $PORTFOLIO_PATH
mkdir $PORTFOLIO_PATH/portfolio

if [ $PORTFOLIO_NAME == "sosp24" ]; then
  setup_sosp24 $PORTFOLIO_PATH/portfolio
elif [ $PORTFOLIO_NAME == "minimal" ]; then
  setup_minimal $PORTFOLIO_PATH/portfolio
fi