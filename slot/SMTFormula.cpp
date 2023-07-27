#include "SMTFormula.h"
#include "SLOTExceptions.h"
#include "SLOTUtil.h"
#include <regex>

#define PLACEHOLDER_WIDTH 2
#define LLVM_FUNCTION_NAME "SMT"
#ifndef PAIR
#define PAIR std::pair<APInt,unsigned>
#endif

namespace SLOT
{
    SMTFormula::SMTFormula(context& t_scx, LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, std::string t_string) : scx(t_scx), lcx(t_lcx), lmodule(t_lmodule), builder(t_builder), string(t_string), contents(t_scx)
    {
        //Regular expression matching to get variables
        std::string s = string;
        std::smatch m;
        std::regex e (R"(\((declare-fun\s(\|.*\||[\~\!\@\$\%\^\&\*_\-\+\=\<\>\.\?\/A-Za-z0-9]+)\s*\(\s*\)\s*(\(\s*_\s*FloatingPoint\s*(\d+)\s*(\d+)\s*\)|Float16|Float32|Float64|Float128|FPN|Real|Int|Bool|\(\s*_\s*BitVec\s*(\d+)\s*\))\s*|declare-const\s(\|.*\||[\~\!\@\$\%\^\&\*_\-\+\=\<\>\.\?\/A-Za-z0-9]+)\s*(\(\s*_\s*FloatingPoint\s*(\d+)\s*(\d+)\s*\)|Float16|Float32|Float64|Float128|FPN|Real|Int|Bool|\(\s*_\s*BitVec\s*(\d+)\s*\))\s*)\))");

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
            else if (m[3]=="Real" || m[8] == "Real")
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

    APInt SMTFormula::LargestIntegerConstant()
    {
        APInt val = APInt();
        for (BooleanNode n : assertions)
        {
            val = APMax(val,n.LargestIntegerConstant());
        }
        return val;
    }

    APInt SMTFormula::AbstractSingle(APInt assumption)
    {
        APInt val = APInt();
        for (BooleanNode n : assertions)
        {
            val = APMax(val,n.AbstractSingle(assumption));
        }
        return val;
    }
    void SMTFormula::ToSMT(unsigned width, solver* sol)
    {
        std::map<std::string, expr> svariables;
        for (auto s : variables)
        {
            //Assumes only integer/boolean values
            //1-wide integer --> boolean
            if (variables[s.first]->getType()->getIntegerBitWidth() == 1)
            {
                svariables.insert(make_pair(s.first, scx.bool_const(s.first.c_str())));
            }
            else
            {
                svariables.insert(make_pair(s.first, scx.bv_const(s.first.c_str(),width)));
            }
        }

        for (BooleanNode n : assertions)
        {
            sol->add(n.ToSMT(width, svariables,sol));
        }
    }





    PAIR SMTFormula::LargestPreciseConstant()
    {
        PAIR val = {APInt(), 0};
        for (BooleanNode n : assertions)
        {
            val = PairMax(val,n.LargestPreciseConstant());
        }
        return val;
    }

    PAIR SMTFormula::AbstractFloat(PAIR assumption)
    {
        PAIR val = {APInt(),0};
        for (BooleanNode n : assertions)
        {
            val = PairMax(val,n.AbstractFloat(assumption));
        }
        return val;
    }
    void SMTFormula::ToSMTFloat(unsigned ebits, unsigned sbits, solver* sol)
    {
        std::map<std::string, expr> svariables;
        for (auto s : variables)
        {
            //Assumes only integer/boolean values
            //1-wide integer --> boolean
            if (variables[s.first]->getType()->getIntegerBitWidth() == 1)
            {
                svariables.insert(make_pair(s.first, scx.bool_const(s.first.c_str())));
            }
            else
            {
                svariables.insert(make_pair(s.first, scx.fpa_const(s.first.c_str(),ebits,sbits)));
            }
        }

        for (BooleanNode n : assertions)
        {
            sol->add(n.ToSMTFloat(scx.fpa_sort(ebits,sbits), svariables));
        }
    }

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

        /*for (unsigned i = 0; i < newModel.size(); i++) 
        {
            func_decl v = newModel[i];
            std::cout << v.to_string() << "   " << newModel.get_const_interp(v).simplify().to_string() << "\n";
            std::cout << m[i].to_string() << "   " << m.get_const_interp(m[i]).simplify().to_string() << "\n";
        }*/

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
    }
}