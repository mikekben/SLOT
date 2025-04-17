## Outline
Python code for SLOT frontend is located in ``frontend.py.`` SLOT backend is ``backend.py``. ``runthrough.sh`` is a shell script run SLOT on an input SMT constraint. ``wrapper.sh`` is a convenient way to run large numbers of benchmarks. ``bv-600-raw.csv`` and ``fp-600-raw.csv`` contain the benchmark results used to generate statistics in the submitted paper. The several ``multiplyOverflow`` files are the motivating example described in the paper.

## Existing results
Results of the bitvector benchmarks used in the evaluation are given in ``bv-600-raw.csv``. ``fp-600-raw.csv`` contains the data for floating point constraints. The first column is the name of the benchmark. Columns 2-5 give the sizes (bytes) of the original constraint, the frontend translation, the optimized LLVM, and backend translation, respectively. Columns 6-8 are the time taken for frontend translation, optimization, and backend translation, in seconds. The remaining columns give the pre-optimization result, pre-optimization time, post-SLOT result, and post-SLOT time. Solvers are in the order Z3, CVC5, and Boolector (for bitvector benchmarks). Any rows for which times are empty indicate that SLOT failed to produce a translation within the 600 second timeout. For evaluation, we count all of these entries as 600 seconds.

## Requirements
Running SLOT requires Python 3, with the following packages installed:
+ Numba LLVMLite: https://github.com/numba/llvmlite (tested with version 0.39.0)
+ Z3 Python bindings: https://pypi.org/project/z3-solver/ (tested with version 0.2.0)

In addition, LLVM opt must be installed. LLVM can be installed with your package manager, or built from source (https://github.com/llvm/llvm-project). If opt is in PATH, then ``runthrough.sh`` should find it. Otherwise, set the ``OPT_CMD`` variable to your optimizer location. ``passes-16.txt`` contains a list of all LLVM 16 passes for ``-O3``, with only those which produce vector instructions removed. To test different optimization passes, you can change the contents of this file. Note that the normal O3 optimization pipeline includes many instcombine passes, most of which are to cleanup the results of irrelevant optimizations.

SLOT supports the following solvers:
+ Z3 can be installed from https://github.com/Z3Prover/z3.
+ CVC5 can be installed from https://github.com/cvc5/cvc5.
+ Boolector can be installed from https://github.com/Boolector/boolector.

SLOT can be run with any (or none) of these solvers. If a solver is in your path, then ``runthrough.sh`` should recognize it. Otherwise, modify the corresponding variable (``Z3``, ``CVC5``, or ``BOOLECTOR``) with the appropriate location.


## Running SLOT
To run SLOT on a particular SMT constraint, use the command,
``./runthrough.sh -z -c -b -t 200 -f multiplyOverflow.smt2``

``runthrough.sh`` takes several flags:
+ ``-r`` (optional) to remove all intermediate files
+ ``-z`` (optional) calls the Z3 SMT solver
+ ``-c`` (optional) calls the CVC5 SMT solver
+ ``-b`` (optional) calls the Boolector solver. Boolector does not support floating point constraints
+ ``-t`` (required) timeout (seconds)
+ ``-f`` (required) the input SMT constraint

## Translation step-by-step

To perform a frontend translation (if -o is omitted, output is written to stdout),
``python3 frontend.py -s multiplyOverflow.smt2 -o multiplyOverflow.ll``

To invoke the optimizer,
``opt multiplyOverflow.ll -O3 -S -o multiplyOverflow-opt.ll``

To perform a backend translation,
``python3 backend.py -l multiplyOverflow-opt.ll -o multiplyOverflow-opt.smt2``

NOTE: LLVMLite does not support recent changes to LLVM debug information, so invoking the above command after optimizing with LLVM 11 or later will produce a backend error. To avoid this error, remove any lines beginning with ``attributes #0`` from the input LLVM file. This is performed automatically by SLOT in the ``runthrough.sh`` script. Using this script instead of manually translating is highly recommended.


## Large-scale testing

To replicate the large-scale testing, first clone the SMTLIB repositories for [QF_BV](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_BV) (>70 GB, requires Git LFS) and [QF_BVFP](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_BVFP) (500 MB). Then invoke SLOT on each benchmark with the desired command line arguments -- ``wrapper.sh`` may be helpful for this purpose. One option for testing is to use GNU parallel with a command like this:
``find QF_BV -name '*.smt2' -type f | parallel ./wrapper.sh >> results.csv``

All experiments were performed on a server with two AMD EPYC 7402 CPUs (96 cores total) and 512GB RAM, running Ubuntu 20.04. In our testing, running on all benchmarks with all solvers took on the order of 48 hours.