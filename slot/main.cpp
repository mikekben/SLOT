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
    std::cout << "This is SLOT.\n";

    if(!HasFlag(argc, argv, "-s"))
    {
        std::cout << "Must specify input file with -s.\n";
        return 1;
    }
    char * inputFilename = GetFlag(argc, argv, "-s");

    //LLVM and Z3 setup
    LLVMContext lcx;
    Module lmodule = Module(inputFilename, lcx);
    IRBuilder builder = IRBuilder(lcx);
    context scx;
    
    std::cout << "done with setup\n";

    //Read from file
    std::ifstream t(inputFilename);
    std::stringstream buffer;
    buffer << t.rdbuf();
    std::string smt_str = buffer.str();


    std::cout << "read from file\n";




    SMTFormula a = SMTFormula(scx, lcx, &lmodule, builder, smt_str);

    std::cout << "made formula\n";

    //Start frontend translation
    a.ToLLVM();


    lmodule.getFunction("SMT")->print(outs());
}