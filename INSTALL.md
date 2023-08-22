# SLOT Installation

## Installation option 1: Docker (recommended)

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



Alternatively, you can build the docker image yourself as follows (note that this re-builds LLVM from scratch and may take more than 30 minutes):

```
docker build -t slot:latest -f slot.dockerfile .
```


## Installation option 2: Manual

To build SLOT locally, follow the following steps:

Download and build LLVM, according to the guide found at https://llvm.org/docs/GettingStarted.html#getting-the-source-code-and-building-llvm.

Building LLVM yourself allows explicit version choice, but you can also install LLVM using your package manager of choice.

Download and build Z3 according to the directions found at https://github.com/Z3Prover/z3. Again, you can also install Z3 using your package manager.

Clone the SLOT repository and navigate the src directory
```
git clone https://github.com/mikekben/SLOT
cd SLOT/src
```
You may have to adjust the paths to LLVM and Z3 in SLOT's Makefile to point to the correct location on your system; this is done by changing the `CPPFLAGS` and `LDLIBS` variables.

Build SLOT:
```
make
cp slot ../
cd ..
```
From this point onwards, simple replications can follow the instructions provided under the docker installation.