## Installation
We suggest you run the experiments using the Docker image we provide.
```
# These commands may require sudo depending on your system configuration.
docker pull cancebeci/tpot:artifact
docker run -it cancebeci/tpot:artifact
```

Or, you can build the Docker container yourself using the Dockerfile included in the repository.
```
# These commands may require sudo depending on your system configuration.
docker build . -t tpot-artifact     # It is normal for Step 12/14 to print warnings.
docker run -it tpot-artifact
```

Alternatively, you can manually install TPot by following the steps below. Please note that we have have only tested building and running TPot with Ubuntu 20.04.
1. Install the dependencies
    ```
    sudo apt update
    sudo apt install -y parallel libz-dev wget unzip build-essential cmake llvm-11 llvm-11-dev llvm-11-tools clang-11 libsqlite3-dev z3 libz3-dev libtcmalloc-minimal4 libgoogle-perftools-dev libunwind-dev jq libgomp1 python3
    pip install lit

    # Install Z3 4.12.2, along with its headers
    mkdir tmp; cd ~/tmp
    wget https://github.com/Z3Prover/z3/archive/refs/tags/z3-4.12.2.zip
    unzip z3-4.12.2.zip 
    cd z3-z3-4.12.2
    python scripts/mk_make.py
    cd build
    make -j$(nproc)
    sudo make install
    cd ../../..
    ```
2. Make sure the right LLVM and Clang versions are used
    ```
    sudo update-alternatives --install /usr/bin/llvm-config llvm-config /usr/bin/llvm-config-11 20
    sudo update-alternatives --install /usr/bin/clang clang /usr/bin/clang-11 20
    sudo update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-11 20
    ```
3. Set up a solver portfolio
    Instead of installing the portfolio we use for our evaluation, you can use a minimal one we are currently experimenting with by replacing `sosp24` with `minimal`.
    ```
    portfolio/setup-portfolio.sh ~/dl/solver-portfolio sosp24
    ```

    Validate that the portfolio was set up correctly. 
    - `~/dl/solver-portfolio` should contain `run-portfolio.sh` and a directory called `portfolio`.
    - `~/dl/solver-portfolio/portfolio` should contain a subdirectory per solver version, and nothing else.
    - For each subdirectory in `~/dl/solver-portfolio/portfolio`, `~/dl/solver-portfolio/portfolio/<subdir>/bin/z3` should be a z3 executable.
4. Build TPot
    ```
    make -j$(nproc) --file=Makefile.common klee-2.3/build/bin/klee
    ```

Once everything is installed, to review our artifact, follow the instructions in `README.md`.
