#include "SMTFormula.h"
#include "LLVMNode.h"
#include <fstream>
#include <streambuf>
#include <sstream>
#include <chrono>

#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/AggressiveInstCombine/AggressiveInstCombine.h"
#include "llvm/Transforms/Scalar/Reassociate.h"
#include "llvm/Transforms/Scalar/SCCP.h"
#include "llvm/Transforms/Scalar/DCE.h"
#include "llvm/Transforms/Scalar/ADCE.h"
#include "llvm/Transforms/Scalar/InstSimplifyPass.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Scalar/EarlyCSE.h"

#ifndef LLMAPPING
#define LLMAPPING std::map<std::string, Value*>&
#endif

#ifndef LLVM_FUNCTION_NAME
#define LLVM_FUNCTION_NAME "SMT"
#endif

using namespace SLOT;
using namespace std::chrono;


void Help()
{
    std::cout << "SLOT arguments:\n";
    std::cout << "   -h             : See help menu\n";
    std::cout << "   -s <file>      : The input SMTLIB2 format file (required)\n";
    std::cout << "   -o <file>      : The output file. If not provided, output is sent to stdout\n";
    std::cout << "   -lu <file>     : Output intermediade LLVM IR before optimization (optional)\n";
    std::cout << "   -lo <file>     : Output intermediade LLVM IR after optimization (optional)\n";
    std::cout << "   -m             : Convert constant shifts to multiplication\n";
    std::cout << "   -t <file>      : Output statistics file. If not provided, output is sent to stdout\n";
    std::cout << "   -pall          : Run all relevant passes (roughly equivalent to -O3 in LLVM). By default, no passes are run\n";
    std::cout << "   -instcombine   : Run instcombine pass\n";
    std::cout << "   -ainstcombine  : Run aggressive instcombine pass\n";
    std::cout << "   -reassociate   : Run reassociate pass\n";
    std::cout << "   -sccp          : Run sparse conditional constant propagation (SCCP) pass\n";
    std::cout << "   -dce           : Run dead code elimination (DCE) pass\n";
    std::cout << "   -adce          : Run aggressive dead code elminination (ADCE) pass\n";
    std::cout << "   -instsimplify  : Run instsimplify pass\n";
    std::cout << "   -gvn           : Run global value numbering (GVN) pass\n";
}

//Not safe: assumes HasFlag returned true and that there is an argument after the flag of interest
char* GetFlag(int argc, char* argv[], const std::string &flag)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (flag.compare(argv[i]) == 0)
    {
      return argv[i+1];
    }
  }
  return 0;
}

bool HasFlag(int argc, char* argv[], const std::string& flag)
{
  for (int i = 1; i < argc; i++)
  {
    if (flag.compare(argv[i]) == 0)
    {
      return true;
    }
  }
  return false;
}

#define INST_COMBINE 1
#define AG_INST_COMBINE 2
#define REASSOCIATE 4
#define SCCP 8
#define DCE 16
#define ADCE 32
#define INST_SIMPLIFY 64
#define GVN 128

unsigned short ParsePasses(int argc, char* argv[])
{
  if (HasFlag(argc, argv, "-pall"))
  {
    return ~0;
  }
  else
  {
    unsigned short toReturn = 0;
    if (HasFlag(argc, argv, "-instcombine")) { toReturn |= INST_COMBINE; }
    if (HasFlag(argc, argv, "-ainstcombine")) { toReturn |= AG_INST_COMBINE; }
    if (HasFlag(argc, argv, "-reassociate")) { toReturn |= REASSOCIATE; }
    if (HasFlag(argc, argv, "-sccp")) { toReturn |= SCCP; }
    if (HasFlag(argc, argv, "-dce")) { toReturn |= DCE; }
    if (HasFlag(argc, argv, "-adce")) { toReturn |= ADCE; }
    if (HasFlag(argc, argv, "-instsimplify")) { toReturn |= INST_SIMPLIFY; }
    if (HasFlag(argc, argv, "-gvn")) { toReturn |= GVN; }
    return toReturn;
  }
}

std::string PrintPasses(unsigned short flags)
{
  return ((flags & INST_COMBINE) ? "1" : "0") + ((std::string)",") +
         ((flags & AG_INST_COMBINE) ? "1" : "0") + "," +
         ((flags & REASSOCIATE) ? "1" : "0") + "," +
         ((flags & SCCP) ? "1" : "0") + "," +
         ((flags & DCE) ? "1" : "0") + "," +
         ((flags & ADCE) ? "1" : "0") + "," +
         ((flags & INST_SIMPLIFY) ? "1" : "0") + "," +
         ((flags & GVN) ? "1" : "0");
}

unsigned short RunPasses(unsigned short flags, Function& fun)
{
  //instcombine and agressive instcombine are run twice, according to the -O3 optimization pass sequence
  LoopAnalysisManager LAM;
  FunctionAnalysisManager FAM;
  CGSCCAnalysisManager CGAM;
  ModuleAnalysisManager MAM;

  PassBuilder PB;

  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  int count = fun.getEntryBlock().sizeWithoutDebug();
  unsigned short used = 0;

  if (flags & INST_COMBINE)
  {
    InstCombinePass().run(fun, FAM);
    if (fun.getEntryBlock().sizeWithoutDebug() != count)
    {
      count = fun.getEntryBlock().sizeWithoutDebug();
      used |= INST_COMBINE;
    }
  }

  if (flags & AG_INST_COMBINE)
  {
    AggressiveInstCombinePass().run(fun, FAM);
    if (fun.getEntryBlock().sizeWithoutDebug() != count)
    {
      count = fun.getEntryBlock().sizeWithoutDebug();
      used |= AG_INST_COMBINE;
    }
  }

  EarlyCSEPass().run(fun, FAM);

  if (flags & REASSOCIATE)
  {
    ReassociatePass().run(fun, FAM);
    if (fun.getEntryBlock().sizeWithoutDebug() != count)
    {
      count = fun.getEntryBlock().sizeWithoutDebug();
      used |= REASSOCIATE;
    }
  }

  if (flags & SCCP)
  {
    SCCPPass().run(fun, FAM);
    if (fun.getEntryBlock().sizeWithoutDebug() != count)
    {
      count = fun.getEntryBlock().sizeWithoutDebug();
      used |= SCCP;
    }
  }

  if (flags & DCE)
  {
    DCEPass().run(fun, FAM);
    if (fun.getEntryBlock().sizeWithoutDebug() != count)
    {
      count = fun.getEntryBlock().sizeWithoutDebug();
      used |= DCE;
    }
  }

  if (flags & ADCE)
  {
    ADCEPass().run(fun, FAM);
    if (fun.getEntryBlock().sizeWithoutDebug() != count)
    {
      count = fun.getEntryBlock().sizeWithoutDebug();
      used |= ADCE;
    }
  }

  if (flags & INST_SIMPLIFY)
  {
    InstSimplifyPass().run(fun, FAM);
    if (fun.getEntryBlock().sizeWithoutDebug() != count)
    {
      count = fun.getEntryBlock().sizeWithoutDebug();
      used |= INST_SIMPLIFY;
    }
  }
  
  if (flags & GVN)
  {
    GVNPass().run(fun, FAM);
    if (fun.getEntryBlock().sizeWithoutDebug() != count)
    {
      count = fun.getEntryBlock().sizeWithoutDebug();
      used |= GVN;
    }
  }

  if (flags & INST_COMBINE)
  {
    InstCombinePass().run(fun, FAM);
    if (fun.getEntryBlock().sizeWithoutDebug() != count)
    {
      count = fun.getEntryBlock().sizeWithoutDebug();
      used |= INST_COMBINE;
    }
  }

  if (flags & AG_INST_COMBINE)
  {
    AggressiveInstCombinePass().run(fun, FAM);
    if (fun.getEntryBlock().sizeWithoutDebug() != count)
    {
      count = fun.getEntryBlock().sizeWithoutDebug();
      used |= AG_INST_COMBINE;
    }
  }

  return used;
}


int LLVMFunction::varCounter = 0;



int main(int argc, char* argv[])
{
  bool shiftToMultiply = false;
  //UI parsing
  if(HasFlag(argc, argv, "-h"))
  {
    Help();
    exit(0);
  }
  if (HasFlag(argc, argv, "-m"))
  {
    shiftToMultiply = true;
  }

  if(!HasFlag(argc, argv, "-s"))
  {
    std::cout << "Must specify input file with -s.\n";
    return 1;
  }
  char * inputFilename = GetFlag(argc, argv, "-s");
  if (!inputFilename)
  {
    std::cout << "Invalid input file name.\n";
    return 1;
  }

  //LLVM and Z3 setup
  LLVMContext lcx;
  Module lmodule = Module(inputFilename, lcx);
  IRBuilder builder = IRBuilder(lcx);

  std::ifstream t(inputFilename);
  std::stringstream buffer;
  buffer << t.rdbuf();
  std::string smt_str = buffer.str();

  
  //Frontend translation
  auto frontStart = high_resolution_clock::now();
  SMTFormula a = SMTFormula(lcx, &lmodule, builder, smt_str, LLVM_FUNCTION_NAME);
  a.ToLLVM();
  auto frontEnd = high_resolution_clock::now();
  duration<double> frontTime = frontEnd - frontStart;
  //Frontend translation



  Function *fun = lmodule.getFunction(LLVM_FUNCTION_NAME);
  unsigned short parsedPasses = ParsePasses(argc, argv);


  char * luFilename;
  if(HasFlag(argc, argv, "-lu") && (luFilename = GetFlag(argc, argv, "-lu")))
  {
    raw_fd_ostream file(luFilename, *(new std::error_code()));
    lmodule.print(file, nullptr);
  }


  //Optimization
  auto optStart = high_resolution_clock::now();
  unsigned short usedPasses = RunPasses(parsedPasses, *fun);
  auto optEnd = high_resolution_clock::now();
  duration<double> optTime = optEnd - optStart;
  //Optimization


  char * loFilename;
  if(HasFlag(argc, argv, "-lo") && (loFilename = GetFlag(argc, argv, "-lo")))
  {
    raw_fd_ostream file(loFilename, *(new std::error_code()));
    lmodule.print(file, nullptr);
  }


  context c;
  solver s(c);


  //Backend translation
  auto backStart = high_resolution_clock::now();
  LLVMFunction f = LLVMFunction(shiftToMultiply, c, fun);
  s.add(f.ToSMT());
  auto backEnd = high_resolution_clock::now();
  duration<double> backTime = backEnd - backStart;
  //Backend translation



  //Print output constraint
  char * outputFilename;
  if(HasFlag(argc, argv, "-o") && (outputFilename = GetFlag(argc, argv, "-o")))
  {
    std::ofstream out(outputFilename);
    out << s.to_smt2();
  }
  else
  {
    std::cout << s.to_smt2();
  }

  //Print statistics
  char * statsFilename;
  if(HasFlag(argc, argv, "-t") && (statsFilename = GetFlag(argc, argv, "-t")))
  {
    std::ofstream out;
    out.open(statsFilename, std::ios_base::app);
    out << inputFilename << "," << (shiftToMultiply ? "true" : "false") << "," << PrintPasses(parsedPasses) << "," << frontTime.count() << "," << optTime.count() << "," << backTime.count() << "," << PrintPasses(usedPasses) << "\n";
  }
  else
  {
    std::cout << inputFilename << "," << (shiftToMultiply ? "true" : "false") << "," << PrintPasses(parsedPasses) << "," << frontTime.count() << "," << optTime.count() << "," << backTime.count() << "," << PrintPasses(usedPasses) << "\n";
  }
  
}