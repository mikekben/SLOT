# SLOT Readme


## About
SLOT (SMT-LLVM Optimizing Translation) is a software tool that speeds up SMT solving in a solver-agnostic way by simplifying constraints. It converts SMT constraints to LLVM, applies the existing LLVM optimizer, and translates back.

SLOT is made publicly available on Github at https://github.com/mikekben/SLOT.

Detailed installation and simple example instructions can be found in [INSTALL.md](INSTALL.md). The recommended option is replicated below for simplicity.

## Recommended installation method with Docker

For ease of use, we have made available a Docker image containing SLOT at https://hub.docker.com/repository/docker/mikekben/slot (~80 GB). This docker image was generated using the provided [dockerfile](./slot.dockerfile). Building SLOT requires a build of LLVM, which may be time consuming. Therefore, we recommend using the pre-built image as follows. Note that the docker run command should automatically pull the image from Dockerhub, but you may also pull it using `docker pull mikekben/slot`


To test SLOT's functionality, run the docker image in interactive mode:
```
docker run -it mikekben/slot
```
and then run SLOT inside the container:

```
./slot -pall -m -s samples/multiplyOverflow.smt2 -lu samples/multiplyOverflow.ll -lo samples/multiplyOverflow-opt.ll -o samples/multiplyOverflow-opt.smt2

#Expected output: samples/multiplyOverflow.smt2,true,1,1,1,1,1,1,1,1,0.0188988,0.0019054,0.00338006,1,0,1,0,1,0,0,0
```

The output above indicates the SLOT has run successfully and shows some statistics about runtime and which optimization passes affected the constraint. The above commands replicate the Motivating Example in the accepted paper, and SLOT's functionality can be verified by inspecting the output in ``samples/multiplyOverflow-opt.smt2``:

```
cat samples/multiplyOverflow-opt.smt2

#Expected output:
(set-info :status unknown)
(assert
 false)
(check-sat)
```

You can also now run both the original constraint and the optimized constraint with a solver to observe the solving time difference:

```
z3/build/z3 samples/multiplyOverflow-opt.smt2

#Expected output (almost instant):
unsat

z3/build/z3 samples/multiplyOverflow.smt2

#Expected output (takes several minutes):
unsat
```


## Further details

The above described method verifies that SLOT has been installed and is working correctly. We also encourage you to apply SLOT to other SMT constraints if you are interested!

The SLOT executable takes the following terminal flags and arguments (which can also be viewed by running `slot -h`).
```
-h            : See help menu
-s <file>     : The input SMTLIB2 format file (required)
-o <file>     : The output file. If not provided, output is sent to stdout
-lu <file>    : Output intermediade LLVM IR before optimization (optional)
-lo <file>    : Output intermediade LLVM IR after optimization (optional)
-m            : Convert constant shifts to multiplication
-t <file>     : Output statistics file. If not provided, output is sent to stdout

#Optimization pass flags. By default, no passes are run

-pall         : Run all relevant passes (roughly equivalent to -O3 in LLVM)
-instcombine  : Run instcombine pass
-ainstcombine : Run aggressive instcombine pass
-reassociate  : Run reassociate pass
-sccp         : Run sparse conditional constant propagation (SCCP) pass
-dce          : Run dead code elimination (DCE) pass
-adce         : Run aggressive dead code elminination (ADCE) pass
-instsimplify : Run instsimplify pass
-gvn          : Run global value numbering (GVN) pass
```
The `-lo` and `-lu` optional flags allow users to see the LLVM IR produced by SLOT before and after optimization. By default, both statistics and the output simplified constraint are sent to stdout, but these can be redirected to files with the `-o` and `-t` flags. Flags are also provided for each of the relevant optimization passes (see the accepted paper for further details), in addition to the `-pall` flag which runs all passes.

SLOT's output statistics take the following form:
```
samples/multiplyOverflow.smt2,true,1,1,1,1,1,1,1,1,0.0188988,0.0019054,0.00338006,1,0,1,0,1,0,0,0
```
This output is, in order, the filename; true or false representing whether the `-m` flag was passed; 8 binary digits representing which of the 8 possible passes was *requested by the user*; three time values (in seconds) corresponding to the amount of time spent on frontend, optimization, and backend; and 8 more binary digits representing which of the 8 possible passes *affected the input constraint*.



For replicability, we also provide the scripts used to run the large scale testing reported in our results section, the raw data collected during those experiments, and a simple Python script used in data analysis. Rerunning the entire benchmark set has substantial hardware requirements and may take more than one week to finish, depending on the available resources.

### Re-running large scale experiments

To test SLOT on the entire SMTLIB benchmark set, follow the following steps:

Clone the three benchmark sets from SMTLIB (about 50GB total, mostly from QF_BV). **Note that some constraints require Git LFS**.
```
git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_BV
git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_FP
git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_BVFP
```

For each of the three benchmark sets, run

```
find ./QF_BV -name '*.smt2' -type f | parallel -j 80 ./wrapper.sh
```
Within `wrapper.sh`, you may adjust the arguments to test with only those solvers you are interested in. If you wish to test with CVC5 or Boolector, you must install those solvers as well. If a solver is not in your path, you may need to adjust the solver variables at the start of `runthrough.sh`. Note that Boolector does not support floating-point constraints.

Replace 80 with the number of threads available on your machine. SMT solving has substantial memory requirements. During our experiments running with 80 threads on a server, memory usage never exceeded ~400 GB. During our experiments, running all three benchmark sets took approximately one week. QF_BV is by far the longest. In addition, the speed of solvers on a particular constraint depends on hardware and other limitations. We therefore focus largely on proportional speedups in our analysis, rather than absolute speedups. 

## Experimental data and analysis

The experimental data collected during our large scale run is provided in `/data`, with one file for each of the three benchmark sets. We also provide a Python script, `analysis.py` which analyzes this data and replicates the tables and statistics found in the accepted paper. To run the analysis, do the following, replacing fp.csv with your benchmark set of choice.

```
cd results
python3 analysis.py -f fp.csv
```