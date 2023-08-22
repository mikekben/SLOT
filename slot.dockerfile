FROM ubuntu:20.04
ENV DEBIAN_FRONTEND noninteractive

RUN apt update
RUN apt install -y git gcc g++ cmake ninja-build python3 zlib1g-dev libtinfo-dev libxml2-dev vim 

WORKDIR /root
RUN git clone https://github.com/llvm/llvm-project
WORKDIR /root/llvm-project
RUN git checkout llvmorg-16.0.0
RUN cmake -S llvm -B build -G Ninja -DCMAKE_BUILD_TYPE=Debug
RUN ninja -j 4 -C build
#Because of docker limitations, Ninja build of LLVM may be memory constrained
#Number of threads can be increased if there is excess memory

WORKDIR /root
RUN git clone https://github.com/Z3Prover/z3
WORKDIR /root/z3
RUN git checkout z3-4.12.1
RUN python3 scripts/mk_make.py
WORKDIR /root/z3/build
RUN make
RUN make install

WORKDIR /root
COPY src ./src
WORKDIR /root/src
RUN make
RUN cp slot ../slot
WORKDIR /root

COPY samples ./samples










