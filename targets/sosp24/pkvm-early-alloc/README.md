#  -- TPot --  
The code in this directory contains a case study originally conducted by Pulte et al.
The original repository is at https://github.com/rems-project/CN-pKVM-early-allocator-case-study

Only the code under `./tpot` is written by the TPot authors.

#  -- Original README -- 
# CN pKVM early allocator case study

This repository contains a small case study, comparing four tools for
the verification of C code: CN, Frama-C, RefinedC, and VeriFast. The
case study is the "early allocator" of the pKVM hypervisor for
Android.

The un-annotated C and header files can be found under
`original`. Each file has a comment recording the original source code
location in the Linux source tree, retaining the original copyright
headers of their authors and license information. 

The files are licensed under GPL-2.0. `GPL-2.0` contains a copy of the GPL-2.0
license. Comments in the files point out where the code has been
modified (minor edits and additions).

The formalisations for the four tools can be found in directories with
their names. The RefinedC formalisation was made by modifying an early
allocator formalisation by Rodolphe Lepigre and Michael Sammler
[[RefinedC
GitLab](https://gitlab.mpi-sws.org/iris/refinedc/-/tree/master/linux/pkvm)],
and doing minor adjustments. The other formalisations are by Dhruv Makwana
and Christopher Pulte.
