CC= g++
CPPFLAGS= -I/root/z3/usr/include -I/z3/src -I/root/llvm-project/build/include -std=c++17 -fno-rtti -D_GNU_SOURCE -D_DEBUG -D_GLIBCXX_ASSERTIONS -D_LIBCPP_ENABLE_ASSERTIONS -D__STDC_CONSTANT_MACROS -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -g -O3 -fexceptions

# Add z3 library flags
Z3_LDFLAGS=-L/root/z3/usr/lib -lz3

# Use llvm-config to get the necessary flags and libraries
LLVM_LDFLAGS=$(shell llvm-config --ldflags)
LLVM_LIBS=$(shell llvm-config --system-libs --libs core passes)

LDLIBS=$(Z3_LDFLAGS) $(LLVM_LDFLAGS) $(LLVM_LIBS)  -lrt -ldl -lpthread -lm -lz -ltinfo -lxml2

main: main.o SMTFormula.o SMTNode.o LLVMFunction.o LLVMNode.o
	$(CC) $(CPPFLAGS) -o slot main.o SMTFormula.o SMTNode.o LLVMFunction.o LLVMNode.o $(LDLIBS)
 
main.o: main.cpp SMTFormula.h SMTNode.h LLVMNode.h SLOTExceptions.h #LLVMFunction.h 
	$(CC) $(CPPFLAGS) -c main.cpp
 
SMTNode.o: SMTNode.h SLOTExceptions.h
	$(CC) $(CPPFLAGS) -c SMTNode.cpp

LLVMNode.o: LLVMNode.h SLOTExceptions.h
	$(CC) $(CPPFLAGS) -c LLVMNode.cpp
 
SMTFormula.o: SMTFormula.h SLOTExceptions.h
	$(CC) $(CPPFLAGS) -c SMTFormula.cpp

LLVMFunction.o: LLVMNode.h SLOTExceptions.h
	$(CC) $(CPPFLAGS) -c LLVMFunction.cpp

clean:
	rm *.o