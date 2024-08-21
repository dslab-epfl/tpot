# Artifact for ‘Practical Verification of System-Software Components Written in Standard C’ at SOSP 24

Thank you for reviewing our artifact! The first step to get started is to install our tool, TPot. For this, please follow the instructions in `INSTALL.md`.

This README recaps the claims made in our paper and provides evidence for each of them.

## Repo organization

- `klee-2.3` contains TPot's source code, which is built on top of [KLEE](https://klee-se.org/).
- `include` contains TPot's API.  
- `portfolio` and `scripts` contain the utilities to setup up TPot and run the experiments for this artifact.
- `targets` containts our case studies, organized as follows:
  * pKVM emem allocator: `targets/sosp24/pkvm-early-alloc/tpot`
  * Vigor allocator: `targets/sosp24/klint/tpot-specs/index_pool`
  * KVM page table: `targets/sosp24/kvm-pgtable`
  * USB driver: `targets/sosp24/usbmouse`
  * Komodo<sup>S</sup>: `targets/sosp24/komodo-serval`
  * Komodo<sup>*</sup>: `targets/sosp24/komodo-star`

## Running POTs
Below, we point to scripts meant to reproduce each result from the paper. If you would like to run the POTs independently of these scripts, use the following commands.

* To verify all targets, run `scripts/verify_sosp24_targets.sh`
* To verify targets one by one, change to the target directory and run `make verify-all`, which runs all the POTs in parallel.
* To run an individual POT, `cd` to the target directory and run `make verify_<POT_NAME>`, for instance `cd targets/sosp24/pkvm-early-alloc/tpot; make verify_spec__alloc_page`.

Each of these commands will first build TPot if it has not already been built.

## Claim: TPot can verify our target components without requiring source code modifications
To validate this claim for each target, change (`cd`) to the target directory, and run `./compare_to_original.sh`.

These scripts fetch the target from the original source, extract the components used in our evaluation, and diff them against our target directory.

The script for Komodo<sup>*</sup> instead prints the diff with respect to Komodo<sup>S</sup>, as the former is a purposeful modification of the latter (Section 5.1 in the paper).

### Explanation of the output:
The diffs output by each script may contain the following:
* Certain external files (Dockerfile, .gitignore, etc.) that are present in original source but not in the TPot target.
* Include statements for TPot primitives (`#include <tpot_primitives.h>`) in some source files in order to override testing primitives (e.g. `assert`) or define the loop invariant primitive `tpot_inv`.
* Loop invariant annotations (calls to `tpot_inv`) as well as definitions for helper functions passed to `tpot_inv`.
* `static` keywords removed from API functions and global data. This is to ensure that POTs can be written in a separate file and still refer to these symbols.

#### Further explanation per target
** USB Driver **
* The definition of `__kernel_size_t` is corrected since the code does not compile otherwise.
* The `usbmouse_verifast.c` file, which is used by the VeriFast case study, makes some modifications on `usbmouse_original.c`. TPot can verify the code with or without these modifications. The diff is computed against `usbmouse_verifast.c`, and includes (as comments) the original code TPot can verify as well.

**KVM page table:**
* The definition of `WARN_ON(b)` provided by the RefinedC case study is corrected from `assert(b)` to `assert(!b)`. This correction is in line with how WARN_ON is used in the Linux tree. 

**Komodo<sup>S</sup>:**
* The optimization level is changed in `config.mk`. This is to ensure that LLVM optimization do not cause unexpected interactions with TPot primitives.
* In `monitor.c`, we enable a section of code from the original Komodo that was removed using an `if 0` directive for the Serval case study.
* In `string.h`, we rename Serval's custom definition of memcpy to `serval_memcpy` for TPot to correctly use our own definition (see `libtpot.c`).
* `include/asm/csr.h` includes `asm/cstate.h` which provides TPot's C models for assembly functions. This is explained further in `asm/cstate.h`.

## Claim: Compared to the baseline verifiers, TPot incurs a lower annotation overhead
We support this claim with the results reported in Table 4. To reproduce this table, change to `targets/sosp24` and run `./loc.sh`.

Note that the table printed by the script is the transpose of the one in the paper: target-verifier pairs are on rows, not columns.

Minor differences from the table found in the paper are expected: they happen because we cleaned up our specifications and automated the line counting when we prepared the artifact.

#### Notes
* In `targets/sosp24/pkvm-early-alloc/loc.sh`, we hardcoded the number of lines of implementation code as `96`. This is the number reported by the [original case study](https://dl.acm.org/doi/pdf/10.1145/3571194), and the number we used to compute annotation overhead in Table 4 in the paper.

  The original case study's counting script (`count.sh`) reports 117 lines. The number 96, reported by the CN paper, is close to that number minus the number of lines found in the `pkvm-early-alloc/original/include` directory (19 according to `cloc original/include`).

* For the Komodo<sup>S</sup> baseline, we omit parts of the global invariant related to reference count correctness.

  The original Serval case study over Komodo organized its proof into three layers: functional correctness specs for the implementation (`spec.rkt`), global invariants over implementation state that are required to prove these specs (`impl.rkt`), and derived properties written over abstract state and expressing invariants over the functional correctness specs themselves (`invariants.rkt`).

  Our case study proves all functional correctness specs and implementation invariants. We additionally prove (directly over implementation state) all derived properties except for those related to reference count correctness.  We count only the lines of Serval code that correspond to things we prove, and leave out the rest.

## Claim: TPot achieves verification times that are compatible with modern CI workflows (< 1 hour)
We support this claim with the results reported in Table 5. To reproduce this table, change to `targets/sosp24` and run `./pot_time.sh`. Similarly to the claim above, this script produces a transposed table.

The CI times reported in the paper are those reported to us by Github CI running on a power machine (2x 12-core Intel Xeon Gold 6248R processors with 384GB RAM, hyperthreading enabled, with Ubuntu 20.04 and Linux kernel 5.4.0.). They are the sum of:

1. Sequentially building/installing all dependencies, then
2. Building TPot, then
3. Running all verification tasks in parallel

To compute the CI time, `pot_time.sh` runs each of the steps above, measuring their duration, and sums up the result. Note that most laptops and desktops will have fewer cores than needed to get full parallelism in step 3, which will lead to higher reported times. 

A notable difference from the verification times reported in the paper is that Komodo<sup>*</sup> is verified much more quickly. This is due to a loop invariant we fixed in `libtpot.c`, avoiding a performance problem that slowed TPot down at the time of our paper submission.
