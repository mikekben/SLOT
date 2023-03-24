CC= g++
CPPFLAGS= -I/nethome/bmikek3/z3/src/api/c++/ -I/nethome/bmikek3/z3/src/api -I/data/qirun/trunk/root-clang/include -std=c++17 -fno-rtti -D_GNU_SOURCE -D_DEBUG -D_GLIBCXX_ASSERTIONS -D_LIBCPP_ENABLE_ASSERTIONS -D__STDC_CONSTANT_MACROS -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -g -O1 -fexceptions
LDLIBS= -L /nethome/bmikek3/z3/build/libz3.so -lz3 -L/data/qirun/trunk/root-clang/lib -lLLVMPasses -lLLVMIRPrinter -lLLVMCoroutines -lLLVMipo -lLLVMInstrumentation -lLLVMVectorize -lLLVMLinker -lLLVMFrontendOpenMP -lLLVMCodeGen -lLLVMTarget -lLLVMScalarOpts -lLLVMInstCombine -lLLVMObjCARCOpts -lLLVMBitWriter -lLLVMAggressiveInstCombine -lLLVMTransformUtils -lLLVMAnalysis -lLLVMProfileData -lLLVMSymbolize -lLLVMDebugInfoPDB -lLLVMDebugInfoMSF -lLLVMDebugInfoDWARF -lLLVMObject -lLLVMTextAPI -lLLVMMCParser -lLLVMIRReader -lLLVMAsmParser -lLLVMMC -lLLVMDebugInfoCodeView -lLLVMBitReader -lLLVMCore -lLLVMRemarks -lLLVMBitstreamReader -lLLVMBinaryFormat -lLLVMTargetParser -lLLVMSupport -lLLVMDemangle -lrt -ldl -lpthread -lm -lz -ltinfo -lxml2


#LDLIBS= -I /nethome/bmikek3/z3/src/api -I /nethome/bmikek3/z3/src/api/c++ -I /nethome/bmikek3/z3/build /nethome/bmikek3/z3/build/libz3.so ``


#-I /nethome/bmikek3/z3/build

#/nethome/qzhang414/trunk/root-clang/bin/llvm-config --cxxflags --ldflags --system-libs --libs core passes
 

 
main: main.o SMTFormula.o SMTNode.o
	$(CC) $(CPPFLAGS) -o main main.o SMTFormula.o SMTNode.o $(LDLIBS)
 
main.o: main.cpp SMTFormula.h SMTNode.h SLOTExceptions.h
	$(CC) $(CPPFLAGS) -c main.cpp
 
SMTNode.o: SMTNode.h SLOTExceptions.h
	$(CC) $(CPPFLAGS) -c SMTNode.cpp
 
SMTFormula.o: SMTFormula.h SLOTExceptions.h
	$(CC) $(CPPFLAGS) -c SMTFormula.cpp

clean:
	rm *.o