#include "SMTFormula.h"
#include <fstream>
#include <streambuf>
#include <sstream>
#include "SLOTUtil.h"

#ifndef PAIR
#define PAIR std::pair<APInt,unsigned>
#endif

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
  //UI parsing
  if(HasFlag(argc, argv, "-h"))
    {
        std::cout << "-s <FILE>               Input .smt2 file\n";
        std::cout << "-o <FILE>               Output .smt2 file\n";
        std::cout << "-t <FILE>               Statistics output file\n";
        std::cout << "-r <ebits,sbits|aix|aix4>    Real numbers: if integer exponent and significant bits are specified, uses those. If aix, uses abstract interpretation. If aix4, uses standard 16/32/64/128 width domain.\n";
        std::cout << "-i <N|aix|aix2>              Integers: if integer N is given uses this fixed withd; if aix, uses abstract interpretation, if aix2, uses abstract interpretation with domain of powers of 2.\n";
        std::cout << "Either real number of integer must be specified.\n";
        return 0;
    }

    if ((!HasFlag(argc, argv, "-r") && !HasFlag(argc, argv, "-i")) || (HasFlag(argc, argv, "-r") && HasFlag(argc, argv, "-i")))
    {
      std::cout << "Must use either -r for real numbers or -i for integers\n";
      return 1;
    }

    bool useInteger;
    int useIntegerWidth = 0;
    int useRealEB = 0;
    int useRealSB = 0;
    if (HasFlag(argc, argv, "-i"))
    {
      useInteger = true;
      std::string val = GetFlag(argc,argv,"-i");
      if(val == "aix")
      {
        useIntegerWidth = -1;
      }
      else
      {
        useIntegerWidth = std::stoi(val);
        assert(useIntegerWidth > 0);
      }
    }
    else
    {
      useInteger = false;
      std::string val = GetFlag(argc,argv,"-r");
      if (val == "aix")
      {
        useRealEB = -1;
        useRealSB = -1;
      }
      else
      {
        std::stringstream ss(val);
        char comma;
        ss >> useRealEB >> comma >> useRealSB;
        assert(useRealEB >= 2);
        assert(useRealSB >= 3);
      }
    }


    if(!HasFlag(argc, argv, "-s"))
    {
        std::cout << "Must specify input file with -s.\n";
        return 1;
    }
    char * inputFilename = GetFlag(argc, argv, "-s");


    std::vector<std::string> stats;
    stats.push_back(inputFilename);


    //LLVM and Z3 setup
    LLVMContext lcx;
    Module lmodule = Module(inputFilename, lcx);
    IRBuilder builder = IRBuilder(lcx);
    context scx;
    scx.set_rounding_mode(RNE);

    //Read from file
    std::ifstream t(inputFilename);
    std::stringstream buffer;
    buffer << t.rdbuf();
    std::string smt_str = buffer.str();
    bool checkResult = true;



    SMTFormula a = SMTFormula(scx, lcx, &lmodule, builder, smt_str);

    solver sol(scx);

    if (useInteger)
    {
      stats.push_back("integer");
      if (useIntegerWidth == -1) //Abstract interpretation case
      {
        //If no constants, assume 1 to model the number of variables
        APInt largest = APMax(APInt(2,1),a.LargestIntegerConstant());
        APInt aiResult = a.AbstractSingle(largest);
        //aiResult.dump();
        //Add 1 for signed, add 1 for buffer
        useIntegerWidth = aiResult.ceilLogBase2()+2;
        useIntegerWidth = useIntegerWidth < 3 ? 3 : useIntegerWidth;
        stats.push_back(toString(largest,10,false).c_str());
        stats.push_back(toString(aiResult,10,false).c_str());
      }
      stats.push_back(std::to_string(useIntegerWidth));
      a.ToSMT(useIntegerWidth,&sol);
    }
    else
    {
      stats.push_back("real");
      if (useRealEB == -1) //Abstract interpretation case
      {
        //If no constants, assume 1 to model the number of variables
        PAIR largest = PairMax({APInt(2,1),1},a.LargestPreciseConstant());
        PAIR aiResult = a.AbstractFloat(largest);
        //Add 1 as buffer; 1 more becuase of sbits semantics in SMTLIB
        unsigned val = aiResult.first.ceilLogBase2()+1;
        useRealEB = 0;
        while (val >>= 1) ++useRealEB; //Integer log_2
        useRealEB++;
        useRealSB = aiResult.second+2;

        useRealEB = useRealEB < 2 ? 2 : useRealEB;
        useRealSB = useRealSB < 3 ? 3 : useRealSB;
        stats.push_back(toString(largest.first,10,false).c_str());
        stats.push_back(std::to_string(largest.second));
        stats.push_back(toString(aiResult.first,10,false).c_str());
        stats.push_back(std::to_string(aiResult.second));
      }
      stats.push_back(std::to_string(useRealEB));
      stats.push_back(std::to_string(useRealSB));
      a.ToSMTFloat(useRealEB,useRealSB,&sol);

    }


    /*char * outputFilename = "./things.smt2";
    std::ofstream out(outputFilename);
    out << sol.to_smt2();
    out.close();*/

    sol.set(":timeout", 300000u);
    sol.set(":memory_max_size", 5120u);

    // initialization
    bool isSat = sol.check() == z3::sat;
    

    if (isSat)
    {
      model m = sol.get_model();
      //std::cout << m.to_string() << "\n";
      //std::cout << "-------\n";
      checkResult = a.CheckAssignment(m);
      if (checkResult)
      {
        stats.push_back("result");
      }
      else
      {
        stats.push_back("sat_underapproximation");
      }
    }
    else
    {
      stats.push_back("unsat_underapproximation");
    }

    if(HasFlag(argc, argv, "-o"))
    {
      char * outputFilename = GetFlag(argc, argv, "-o");
      std::ofstream out(outputFilename);
      out << sol.to_smt2();
      out.close();
    }


    char * statFilename;

    if (HasFlag(argc, argv, "-t") && (statFilename = GetFlag(argc, argv, "-t")))
    {
      std::ofstream stat_out(statFilename, std::ios_base::app);
      for (std::string s : stats)
      {
        stat_out << s;
        stat_out << ",";
      }
      stat_out << "\n";
      stat_out.close();
    }
    else
    {
      for (std::string s : stats)
      {
        std::cout << s;
        std::cout << ",";
      }
      std::cout << "\n";
    }
    exit(0);
}