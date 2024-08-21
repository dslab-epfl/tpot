# Dockerfile for setting up and building TPot project on Ubuntu 22.04

# Start from a base Ubuntu 22.04 image
FROM ubuntu:22.04


# Update and install dependencies
# Create ``tpot`` user for container with password ``tpot``
# and give it password-less sudo access
RUN apt-get update && \
    DEBIAN_FRONTEND=noninteractive apt-get install -y \
        sudo \
        parallel \
        libz-dev \
        wget \
        unzip \
        build-essential \
        cmake \
        llvm-11 \
        llvm-11-dev \
        llvm-11-tools \
        clang-11 \
        libsqlite3-dev \
        z3 \
        libz3-dev \
        libtcmalloc-minimal4 \
        libgoogle-perftools-dev \
        libunwind-dev \
        vim \
        cloc \
        bc \
        nano && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

# Install Z3 4.4.1
RUN wget -q https://github.com/Z3Prover/z3/releases/download/z3-4.4.1/z3-4.4.1-x64-ubuntu-14.04.zip && \
    unzip -q z3-4.4.1-x64-ubuntu-14.04.zip && \
    cp z3-4.4.1-x64-ubuntu-14.04/bin/* /usr/bin/ && \
    cp z3-4.4.1-x64-ubuntu-14.04/include/* /usr/include/ && \
    rm -rf z3-4.4.1-x64-ubuntu-14.04.zip z3-4.4.1-x64-ubuntu-14.04

# Use LLVM 11
RUN update-alternatives --install /usr/bin/llvm-config llvm-config /usr/bin/llvm-config-11 20 && \
    update-alternatives --install /usr/bin/clang clang /usr/bin/clang-11 20 && \
    update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-11 20

# Create tpot user
RUN useradd -m tpot && \
    echo tpot:tpot | chpasswd && \
    touch /etc/sudoers && \
    cp /etc/sudoers /etc/sudoers.bak && \
    echo 'tpot  ALL=(root) NOPASSWD: ALL' >> /etc/sudoers

# Grant necessary permissions to tpot user
RUN mkdir -p /home/tpot && chown -R tpot:tpot /home/tpot

# Switch to tpot user
USER tpot

# Set the working directory and copy the project files under 'tpot' user
WORKDIR /home/tpot/tpot
COPY --chown=tpot:tpot . .

# Setup portfolio Z3 under 'tpot' user
RUN portfolio/setup-portfolio.sh ~/dl/solver-portfolio minimal

# Build the project under 'tpot' user
RUN make -j$(nproc) --file=Makefile.common klee-2.3/build/bin/klee

# Add to path
ENV PATH="$PATH:/home/tpot/tpot/klee-2.3/build/bin"

WORKDIR /home/tpot/tpot
