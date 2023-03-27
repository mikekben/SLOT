#include "SMTFormula.h"
#include <fstream>
#include <streambuf>
#include <sstream>

using namespace SLOT;

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


int main(int argc, char* argv[])
{

    if(!HasFlag(argc, argv, "-s"))
    {
        std::cout << "Must specify input file with -s.\n";
        return 1;
    }
    char * inputFilename = GetFlag(argc, argv, "-s");

    if(!HasFlag(argc, argv, "-o"))
    {
        std::cout << "Must specify output file with -o.\n";
        return 1;
    }
    char * outputFilename = GetFlag(argc, argv, "-o");

    //LLVM and Z3 setup
    LLVMContext lcx;
    Module lmodule = Module(inputFilename, lcx);
    IRBuilder builder = IRBuilder(lcx);
    context scx;

    //Read from file
    std::ifstream t(inputFilename);
    std::stringstream buffer;
    buffer << t.rdbuf();
    std::string smt_str = buffer.str();





    SMTFormula a = SMTFormula(scx, lcx, &lmodule, builder, smt_str);

    APInt largest = a.LargestIntegerConstant();
    APInt aiResult = a.AbstractSingle(largest);
    //Add 1 for signed, add 1 for buffer
    unsigned width = aiResult.ceilLogBase2()+2;

    solver sol(scx);

    a.ToSMT(width,&sol);
    //std::cout << sol.to_smt2() << "\n";

    //Write to file
    std::ofstream out(outputFilename);
    out << sol.to_smt2();
    out.close();


    char * statFilename;
    //Print used pass information
    if (HasFlag(argc, argv, "-t") && (statFilename = GetFlag(argc, argv, "-t")))
    {
      std::ofstream stat_out(statFilename, std::ios_base::app);
      stat_out << inputFilename << "," << toString(largest,10,false).c_str() << "," << toString(aiResult,10,false).c_str() << "," << width << "\n";
      stat_out.close();
    }  


    exit(0);
}