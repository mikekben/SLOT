#include "SMTFormula.h"
#include "SLOTExceptions.h"
#include <regex>

#ifndef LLMAPPING
#define LLMAPPING std::map<std::string, Value*>
#endif

namespace SLOT
{
    static context c;

    SMTFormula::SMTFormula(LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, std::string t_string, std::string t_func_name) : lcx(t_lcx), lmodule(t_lmodule), builder(t_builder), string(t_string), contents(c), func_name(t_func_name)
    {
        //context c;
        //Regular expression matching to get variables
        std::string s = string;
        std::smatch m;
        std::regex e (R"(\((declare-fun\s(\|.*\||[\~\!\@\$\%\^\&\*_\-\+\=\<\>\.\?\/A-Za-z0-9]+)\s*\(\s*\)\s*(\(\s*_\s*FloatingPoint\s*(\d+)\s*(\d+)\s*\)|Float16|Float32|Float64|Float128|FPN|Bool|\(\s*_\s*BitVec\s*(\d+)\s*\))\s*|declare-const\s(\|.*\||[\~\!\@\$\%\^\&\*_\-\+\=\<\>\.\?\/A-Za-z0-9]+)\s*(\(\s*_\s*FloatingPoint\s*(\d+)\s*(\d+)\s*\)|Float16|Float32|Float64|Float128|FPN|Bool|\(\s*_\s*BitVec\s*(\d+)\s*\))\s*)\))");

        std::vector<Type*> types;
        std::vector<std::string> names;
        std::string temp = "";
        while (std::regex_search(s, m, e))
        {
            if (m[2]!="")
            {
                temp = m[2];
            }
            else
            {
                temp = m[7];
            }

            if (temp[0] == '|')
            {
                names.push_back(temp.substr(1, temp.length() - 2));
            }
            else
            {
                names.push_back(temp);
            }
            
            if (m[3]=="Bool" || m[8] == "Bool") //Boolean
            {
                types.push_back(Type::getInt1Ty(lcx));
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
                throw UnsupportedTypeException("unsupported SMT variable type", names.back());
            }
            s = m.suffix().str();
        }


        //Create function
        FunctionType* fnty = FunctionType::get(Type::getInt1Ty(lcx),types,false);
        function = Function::Create(fnty, Function::ExternalLinkage, func_name, lmodule);
        //Assign variable types
        int i = 0;
        for (auto &arg : function->args())
        {
            arg.setName(names[i]);
            variables[names[i]] = &arg;
            i++;
        }

        contents = c.parse_string(t_string.c_str());

        for (expr e : contents)
        {
            assertions.push_back(BooleanNode(lcx, lmodule, builder, variables, e));
        }

        //assert(assertions.size() >= 1);
    }

    void SMTFormula::ToLLVM()
    {
        BasicBlock* bb = BasicBlock::Create(lcx, "b", function);
        builder.SetInsertPoint(bb);
        
        if (assertions.size() == 0)
        {
            //Empty constraint is sat
            builder.CreateRet(ConstantInt::getBool(lcx, true));
        }
        else
        {
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

    
/*
    bool SMTFormula::CheckAssignment(model m)
    {
        solver sol(scx);

        sol.add(contents);

        model newModel(scx);
        // traversing the model
        for (unsigned i = 0; i < m.size(); i++) 
        {
            func_decl v = m[i];
            assert(v.arity() == 0); 
            expr interpretation = m.get_const_interp(v);
            expr temp(scx);
            func_decl declaration(scx);

            if (interpretation.is_bool())
            {
                newModel.add_const_interp(v,interpretation);
            }
            else if (interpretation.is_bv())
            {
                temp = bv2int(interpretation, true);
                declaration = scx.function(v.name(), 0, NULL, scx.int_sort());
                newModel.add_const_interp(declaration,temp);
            }
            else if (interpretation.is_fpa())
            {
                temp = expr(scx,Z3_mk_fpa_to_real(scx, interpretation));
                declaration = scx.function(v.name(),0,NULL,scx.real_sort());
                newModel.add_const_interp(declaration,temp);
            }
        }

        for (expr e : contents)
        {
            //std::cout << e << "\n";
            expr val = newModel.eval(e);
            //std::cout << val.simplify() << "\n";
            if (!val.simplify().is_true())
            {
                return false;
            }
        }
        return true;
        //expr result = newModel.eval(expr(scx,contents));
        //std::cout << result.to_string() << "\n";
        //return result.is_true();
    }*/
}