CC= g++
CPPFLAGS= -I/root/z3/src/api/c++/ -I/root/z3/src/api -I/root/llvm-project/build/include -I/root/llvm-project/llvm/include -std=c++17 -fno-rtti -D_GNU_SOURCE -D_DEBUG -D_GLIBCXX_ASSERTIONS -D_LIBCPP_ENABLE_ASSERTIONS -D__STDC_CONSTANT_MACROS -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -g -O3 -fexceptions
LDLIBS= -L/root/z3/build/libz3.so -lz3 -L/root/llvm-project/build/lib -lLLVMPasses -lLLVMIRPrinter -lLLVMCoroutines -lLLVMipo -lLLVMInstrumentation -lLLVMVectorize -lLLVMLinker -lLLVMFrontendOpenMP -lLLVMCodeGen -lLLVMTarget -lLLVMScalarOpts -lLLVMInstCombine -lLLVMObjCARCOpts -lLLVMBitWriter -lLLVMAggressiveInstCombine -lLLVMTransformUtils -lLLVMAnalysis -lLLVMProfileData -lLLVMSymbolize -lLLVMDebugInfoPDB -lLLVMDebugInfoMSF -lLLVMDebugInfoDWARF -lLLVMObject -lLLVMTextAPI -lLLVMMCParser -lLLVMIRReader -lLLVMAsmParser -lLLVMMC -lLLVMDebugInfoCodeView -lLLVMBitReader -lLLVMCore -lLLVMRemarks -lLLVMBitstreamReader -lLLVMBinaryFormat -lLLVMTargetParser -lLLVMSupport -lLLVMDemangle -lrt -ldl -lpthread -lm -lz -ltinfo -lxml2

 
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