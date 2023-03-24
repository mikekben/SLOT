#include "SMTFormula.h"
#include "SLOTExceptions.h"
#include <regex>

#define PLACEHOLDER_WIDTH 1
#define LLVM_FUNCTION_NAME "SMT"

namespace SLOT
{
    SMTFormula::SMTFormula(context& t_scx, LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, std::string t_string) : scx(t_scx), lcx(t_lcx), lmodule(t_lmodule), builder(t_builder), string(t_string), contents(t_scx)
    {
        //Regular expression matching to get variables
        std::string s = string;
        std::smatch m;
        std::regex e (R"(\((declare-fun\s(\|.*\||[\~\!\@\$\%\^\&\*_\-\+\=\<\>\.\?\/A-Za-z0-9]+)\s*\(\s*\)\s*(\(\s*_\s*FloatingPoint\s*(\d+)\s*(\d+)\s*\)|Float16|Float32|Float64|Float128|FPN|Int|Bool|\(\s*_\s*BitVec\s*(\d+)\s*\))\s*|declare-const\s(\|.*\||[\~\!\@\$\%\^\&\*_\-\+\=\<\>\.\?\/A-Za-z0-9]+)\s*(\(\s*_\s*FloatingPoint\s*(\d+)\s*(\d+)\s*\)|Float16|Float32|Float64|Float128|FPN|Int|Bool|\(\s*_\s*BitVec\s*(\d+)\s*\))\s*)\))");

        std::cout << "starting regex\n";
        std::vector<Type*> types;
        std::vector<std::string> names;
        while (std::regex_search (s,m,e)) 
        {
            if (m[2]!="")
            {
                names.push_back(m[2]);
            }
            else
            {
                names.push_back(m[7]);
            }
            
            if (m[3]=="Bool" || m[8] == "Bool") //Boolean
            {
                types.push_back(Type::getInt1Ty(lcx));
            }
            else if (m[3]=="Int" || m[8] == "Int") //Integer
            {
                types.push_back(Type::getIntNTy(lcx,PLACEHOLDER_WIDTH));
            }
            else if (m[6] != "") //Bitvector
            {
                types.push_back(Type::getIntNTy(lcx,stoi(m[6].str())));
            }
            else if (m[11] != "")
            {
                types.push_back(Type::getIntNTy(lcx,stoi(m[11].str())));
            }
            else if (m[4] != "" && m[5] != "") //General floating point
            {
                types.push_back(FloatingNode::ToFloatingType(lcx,names.back(),stoi(m[4])+stoi(m[5])));
            }
            else if (m[9] != "" && m[10] != "") 
            {
                types.push_back(FloatingNode::ToFloatingType(lcx,names.back(),stoi(m[9])+stoi(m[10])));
            }
            else if (m[3]=="Float16" || m[3]=="Float32" || m[3]=="Float64" || m[3]=="Float128") //Named floating points
            {
                types.push_back(FloatingNode::ToFloatingType(lcx,names.back(),stoi(m[3].str().substr(5))));
            }
            else if (m[8]=="Float16" || m[8]=="Float32" || m[8]=="Float64" || m[8]=="Float128") //Named floating points
            {
                types.push_back(FloatingNode::ToFloatingType(lcx,names.back(),stoi(m[8].str().substr(5))));
            }
            else if (m[3]=="FPN" || m[8]=="FPN") //Special case for the convention (define-sort FPN () (_ FloatingPoint 11 53)) in QF_FP
            {
                types.push_back(FloatingNode::ToFloatingType(lcx,names.back(),64));
            }
            else
            {
                throw UnsupportedSMTTypeException("unsupported type", names.back());
            }
            s = m.suffix().str();
        }

        std::cout << "done with regex\n";

        //Create function
        FunctionType* fnty = FunctionType::get(Type::getInt1Ty(lcx),types,false);
        function = Function::Create(fnty, Function::ExternalLinkage, LLVM_FUNCTION_NAME, lmodule);
        //Assign variable types
        int i = 0;
        for (auto &arg : function->args())
        {
            arg.setName(names[i]);
            variables[names[i]] = &arg;
            i++;
        }

        contents = scx.parse_string(t_string.c_str());

        for (expr e : contents)
        {
            assertions.push_back(BooleanNode(scx, lcx, lmodule, builder, PLACEHOLDER_WIDTH, variables, e));
        }

        assert(assertions.size() >= 1);
    }

    void SMTFormula::ToLLVM() 
    {
        BasicBlock* bb = BasicBlock::Create(lcx, "b", function);
        builder.SetInsertPoint(bb);

        Value* temp = assertions[0].ToLLVM();
        //Conjunction of all assertions
        if (assertions.size() > 1)
        {
            for (int i = 1; i < assertions.size(); i++)
            {
                temp = builder.CreateAnd(temp,assertions[i].ToLLVM());
            }
        }

        builder.CreateRet(temp);
    }
}