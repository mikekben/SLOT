# SLOT Requirements

## For installation with pre-built Docker image:
At lest 100GB of free storage
At least 8GB of memory

+ Ubuntu (tested with version 20.04)
+ A recent version of Docker

## For building Docker image:
At least 100GB of free storage
At least 64GB of memory. 

Note that the memory requirement can be reduced by changing the number of threads in the Ninja build of LLVM on line 12 of the dockerfile--there is a tradeoff between memory consumption and speed of build. The substantial memory requirements are associated with building LLVM, not SLOT perse. If you have a pre-existing build of LLVM, you can also copy this build into the docker container to save time.

+ Ubuntu (tested with version 20.04)
+ A recent version of Docker


## For manual builds:
At least 100GB of free storage
At least 8GB of memory. 

+ Ubuntu (tested with version 20.04)
+ git 
+ gcc 
+ g++ 
+ cmake (for building LLVM)
+ ninja-build (for building LLVM)
+ python3 (for building Z3)
+ zlib1g-dev 
+ libtinfo-dev
+ libxml2-dev