#include "SMTNode.h"
#include "SLOTExceptions.h"
#include "SLOTUtil.h"

namespace SLOT
{
    //Syntax sugar for extracting children
    inline IntegerNode SMTNode::IntegerChild(expr cont) { return IntegerNode(scx,lcx,lmodule,builder,integer_width,variables,cont); }
    inline IntegerNode SMTNode::IntegerChild(int index) { return IntegerNode(scx,lcx,lmodule,builder,integer_width,variables,contents.arg(index)); }
    inline FloatingNode SMTNode::FloatingChild(expr cont) { return FloatingNode(scx,lcx,lmodule,builder,integer_width,variables,cont); }
    inline FloatingNode SMTNode::FloatingChild(int index) { return FloatingNode(scx,lcx,lmodule,builder,integer_width,variables,contents.arg(index)); }
    inline BitvectorNode SMTNode::BitvectorChild(expr cont) { return BitvectorNode(scx,lcx,lmodule,builder,integer_width,variables,cont); }
    inline BitvectorNode SMTNode::BitvectorChild(int index) { return BitvectorNode(scx,lcx,lmodule,builder,integer_width,variables,contents.arg(index)); }
    inline BooleanNode SMTNode::BooleanChild(expr cont) { return BooleanNode(scx,lcx,lmodule,builder,integer_width,variables,cont); }
    inline BooleanNode SMTNode::BooleanChild(int index) { return BooleanNode(scx,lcx,lmodule,builder,integer_width,variables,contents.arg(index)); }

    SMTNode::SMTNode(context& t_scx, LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, unsigned t_integer_width, const std::map<std::string, Value*>& t_variables, expr t_contents) : scx(t_scx), lcx(t_lcx), lmodule(t_lmodule), builder(t_builder), integer_width(t_integer_width), variables(t_variables), contents(t_contents)
    {

    }


    //============================IntegerNode==================================

    bool IntegerNode::IsComparison(expr expression) //static
    {
        Z3_decl_kind k = expression.decl().decl_kind();
        bool direct = (k == Z3_OP_LE || k == Z3_OP_LT || k == Z3_OP_GE || k == Z3_OP_GT);
        return expression.num_args() >= 1 && expression.arg(0).is_int() && (expression.is_eq() || expression.is_distinct() || direct);
    }

    IntegerNode::IntegerNode(context& t_scx, LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, unsigned t_integer_width, const std::map<std::string, Value*>& t_variables, expr t_contents) : SMTNode(t_scx, t_lcx, t_lmodule, t_builder, t_integer_width, t_variables, t_contents)
    {
        //Sanity check for translation from Z3 expresssions
        assert(contents.is_int());
    }

    Value* IntegerNode::ToLLVM()
    {
        if (IsVariable())
        {
            return variables.at(contents.to_string());
        }
        else if (IsConstant())
        {
            //Handle negative constants
            std::string str = contents.to_string();
            if (str[0]=='(' && str[1]=='-')
            {
                str.erase(0,1);
                str.erase(2,1);
                str.erase(str.length()-1,1);
            }
            return ConstantInt::get(IntegerType::get(lcx, Width()), str, 10);
        }
        else //Expression
        {
            switch (Op())
            {
                case Z3_OP_ITE:
                    return builder.CreateSelect(BooleanChild(0).ToLLVM(),IntegerChild(1).ToLLVM(),IntegerChild(2).ToLLVM());
                case Z3_OP_UMINUS:
                    return builder.CreateSub(ConstantInt::get(IntegerType::get(lcx, Width()), 0),IntegerChild(0).ToLLVM());
                case Z3_OP_SUB:
                    return builder.CreateSub(IntegerChild(0).ToLLVM(),IntegerChild(1).ToLLVM());
                case Z3_OP_ADD:
                    return builder.CreateAdd(IntegerChild(0).ToLLVM(),IntegerChild(1).ToLLVM());
                case Z3_OP_MUL:
                    return builder.CreateMul(IntegerChild(0).ToLLVM(),IntegerChild(1).ToLLVM());
                case Z3_OP_IDIV:
                    return builder.CreateSDiv(IntegerChild(0).ToLLVM(),IntegerChild(1).ToLLVM());
                case Z3_OP_MOD:
                    return builder.CreateSRem(IntegerChild(0).ToLLVM(),IntegerChild(1).ToLLVM());
                default:
                    throw UnsupportedSMTOpException("integer operation", contents);
            }
        }
    }
    APInt IntegerNode::LargestIntegerConstant()
    {
        if (IsVariable())
        {
            return APInt();
        }
        else if (IsConstant())
        {
            //Handle negative constants
            std::string str = contents.to_string();
            if (str[0]=='(' && str[1]=='-')
            {
                str.erase(0,1);
                str.erase(1,1);
                str.erase(str.length()-1,1);
            }

            //Length in base 10 * 4 (log_2(10) + 1) to guarantee enough width
            return APInt(str.length()*4, str, 10).abs();
        }
        //Expressions (TODO: assumes only integer constraints in children)
        else if (Op() == Z3_OP_ITE)
        {
            APInt cond = BooleanChild(0).LargestIntegerConstant();
            APInt left = IntegerChild(1).LargestIntegerConstant();
            APInt right = IntegerChild(2).LargestIntegerConstant();
            return APMax(cond,APMax(left,right));
        }
        else if (Op() == Z3_OP_UMINUS)
        {
            return IntegerChild(0).LargestIntegerConstant();
        }
        else if (Op() == Z3_OP_INTERNAL) //integer absolute value
        {
            return IntegerChild(0).LargestIntegerConstant();
        }
        else //Binary integer expressions
        {
            return APMax(IntegerChild(0).LargestIntegerConstant(),IntegerChild(1).LargestIntegerConstant());
        }
    }
    APInt IntegerNode::AbstractSingle(APInt assumption)
    {
        if (IsVariable())
        {
            return assumption;
        }
        else if (IsConstant())
        {
            //Handle negative constants
            std::string str = contents.to_string();
            if (str[0]=='(' && str[1]=='-')
            {
                str.erase(0,1);
                str.erase(1,1);
                str.erase(str.length()-1,1);
            }

            //Length in base 10 * 4 (log_2(10) + 1) to guarantee enough width
            return APInt(str.length()*4, str, 10).abs();
        }
        else //Expression
        {
            APInt left;
            APInt right;
            unsigned bigger;
            switch (Op())
            {

                case Z3_OP_ITE:
                    //Take whichever branch is bigger
                    return APMax(IntegerChild(1).AbstractSingle(assumption), IntegerChild(2).AbstractSingle(assumption));
                case Z3_OP_UMINUS:
                case Z3_OP_INTERNAL: //Integer absolute value
                    //Only absolute value
                    return IntegerChild(0).AbstractSingle(assumption);
                case Z3_OP_SUB:
                case Z3_OP_ADD:
                    //Subtraction and addition can both grow (absolute value)
                    return APPlus(IntegerChild(0).AbstractSingle(assumption),IntegerChild(1).AbstractSingle(assumption));
                case Z3_OP_MUL:
                    return APMult(IntegerChild(0).AbstractSingle(assumption),IntegerChild(1).AbstractSingle(assumption));
                case Z3_OP_IDIV:
                    //Can't add extra bits
                    return APDiv(IntegerChild(0).AbstractSingle(assumption),IntegerChild(1).AbstractSingle(assumption));
                case Z3_OP_MOD:
                    //Remainder is always smaller than divisor
                    return IntegerChild(1).AbstractSingle(assumption);
                default:
                    throw UnsupportedSMTOpException("integer operation", contents);
            }
        }
    }

    expr IntegerNode::ToSMT(unsigned width, std::map<std::string, expr> svariables)
    {
        if (IsVariable())
        {
            return svariables.at(contents.to_string());
        }
        else if (IsConstant())
        {
            //Handle negative constants
            std::string str = contents.to_string();
            if (str[0]=='(' && str[1]=='-')
            {
                str.erase(0,1);
                str.erase(1,1);
                str.erase(str.length()-1,1);
            }

            return scx.bv_val(str.c_str(), width);
        }
        else //Expression
        {
            expr val = scx.bool_val(true);
            switch (Op())
            {
                case Z3_OP_ITE:
                    return ite(BooleanChild(0).ToSMT(width,svariables),IntegerChild(1).ToSMT(width,svariables),IntegerChild(2).ToSMT(width,svariables));
                case Z3_OP_UMINUS:
                    return -IntegerChild(0).ToSMT(width,svariables);
                case Z3_OP_INTERNAL: //integer absolute value
                    val = IntegerChild(0).ToSMT(width,svariables);
                    return ite(val < 0, -val, val);
                case Z3_OP_SUB:
                    return IntegerChild(0).ToSMT(width,svariables) - IntegerChild(1).ToSMT(width,svariables);
                case Z3_OP_ADD:
                    return IntegerChild(0).ToSMT(width,svariables) + IntegerChild(1).ToSMT(width,svariables);
                case Z3_OP_MUL:
                    return IntegerChild(0).ToSMT(width,svariables) * IntegerChild(1).ToSMT(width,svariables);
                case Z3_OP_IDIV:
                    //division operator overload is signed division
                    return IntegerChild(0).ToSMT(width,svariables) / IntegerChild(1).ToSMT(width,svariables);
                case Z3_OP_MOD:
                    return mod(IntegerChild(0).ToSMT(width,svariables),IntegerChild(1).ToSMT(width,svariables));
                default:
                    throw UnsupportedSMTOpException("integer operation", contents);
            }
        }
    }


    //============================BooleanNode==================================


    BooleanNode::BooleanNode(context& t_scx, LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, unsigned t_integer_width, const std::map<std::string, Value*>& t_variables, expr t_contents) : SMTNode(t_scx, t_lcx, t_lmodule, t_builder, t_integer_width, t_variables, t_contents)
    {
        //Sanity check for translation from Z3 expresssions
        assert(contents.is_bool());
    }

    Value* BooleanNode::ToLLVM()
    {
        if (IsVariable())
        {
            return variables.at(contents.to_string());
        }
        else if (IsConstant())
        {
            return ConstantInt::getBool(lcx, contents.is_true());
        }
        else //Expression case
        {
            Value* temp;
            switch (Op())
            {
                //Boolean only operations
                case Z3_OP_NOT:
                    return builder.CreateNot(BooleanChild(0).ToLLVM());
                case Z3_OP_AND:
                    temp = BooleanChild(0).ToLLVM();
                    for (int i = 1; i < contents.num_args(); i++)
                    {
                        temp = builder.CreateAnd(temp,BooleanChild(i).ToLLVM());
                    }
                    return temp;
                case Z3_OP_OR:
                    temp = BooleanChild(0).ToLLVM();
                    for (int i = 1; i < contents.num_args(); i++)
                    {
                        temp = builder.CreateOr(temp,BooleanChild(i).ToLLVM());
                    }
                    return temp;
                case Z3_OP_XOR:
                    temp = BooleanChild(0).ToLLVM();
                    for (int i = 1; i < contents.num_args(); i++)
                    {
                        temp = builder.CreateXor(temp,BooleanChild(i).ToLLVM());
                    }
                    return temp;
                case Z3_OP_IMPLIES:
                    return builder.CreateOr(builder.CreateNot(BooleanChild(0).ToLLVM()),BooleanChild(1).ToLLVM());
                case Z3_OP_ITE:
                    return builder.CreateSelect(BooleanChild(0).ToLLVM(),BooleanChild(1).ToLLVM(),BooleanChild(2).ToLLVM());
                //Integer comparisons
                case Z3_OP_LE:
                    return builder.CreateICmpSLE(IntegerChild(0).ToLLVM(), IntegerChild(1).ToLLVM());
                case Z3_OP_LT:
                    return builder.CreateICmpSLT(IntegerChild(0).ToLLVM(), IntegerChild(1).ToLLVM());
                case Z3_OP_GE:
                    return builder.CreateICmpSGE(IntegerChild(0).ToLLVM(), IntegerChild(1).ToLLVM());
                case Z3_OP_GT:
                    return builder.CreateICmpSGT(IntegerChild(0).ToLLVM(), IntegerChild(1).ToLLVM());
                //Bitvector comparisons
                case Z3_OP_SLEQ:
                    return builder.CreateICmpSLE(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                case Z3_OP_SGEQ:
                    return builder.CreateICmpSGE(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                case Z3_OP_SLT:
                    return builder.CreateICmpSLT(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                case Z3_OP_SGT:
                    return builder.CreateICmpSGT(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                case Z3_OP_ULEQ:
                    return builder.CreateICmpULE(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                case Z3_OP_UGEQ:
                    return builder.CreateICmpUGE(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                case Z3_OP_ULT:
                    return builder.CreateICmpULT(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                case Z3_OP_UGT:
                    return builder.CreateICmpUGT(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                //Floating comparisons. All comparisons are ordered
                //(SMT LIB says comparison is false if either argument is NAN)
                case Z3_OP_FPA_EQ:
                    return builder.CreateFCmpOEQ(FloatingChild(0).ToLLVM(), FloatingChild(1).ToLLVM());
                case Z3_OP_FPA_LT:
                    return builder.CreateFCmpOLT(FloatingChild(0).ToLLVM(), FloatingChild(1).ToLLVM());
                case Z3_OP_FPA_GT:
                    return builder.CreateFCmpOGT(FloatingChild(0).ToLLVM(), FloatingChild(1).ToLLVM());
                case Z3_OP_FPA_LE:
                    return builder.CreateFCmpOLE(FloatingChild(0).ToLLVM(), FloatingChild(1).ToLLVM());
                case Z3_OP_FPA_GE:
                    return builder.CreateFCmpOGE(FloatingChild(0).ToLLVM(), FloatingChild(1).ToLLVM());
                //Floating class checks
                case Z3_OP_FPA_IS_NAN: 
                case Z3_OP_FPA_IS_INF: 
                case Z3_OP_FPA_IS_ZERO: 
                case Z3_OP_FPA_IS_NORMAL: 
                case Z3_OP_FPA_IS_SUBNORMAL: 
                case Z3_OP_FPA_IS_NEGATIVE: 
                case Z3_OP_FPA_IS_POSITIVE:
                    return FloatingChild(0).LLVMClassCheck(Op());
                //equal and distinct comparisons (children can be any sort)
                case Z3_OP_EQ:
                    //Z3 parser converts = with more than 2 children into pairwise checks
                    assert(contents.num_args()==2);
                    //Boolean, bitvector, and integer are all integer (bitwise) comparison
                    if (contents.arg(0).is_bool())
                    {
                        return builder.CreateICmpEQ(BooleanChild(0).ToLLVM(),BooleanChild(1).ToLLVM());
                    }
                    else if (contents.arg(0).is_bv())
                    {
                        return builder.CreateICmpEQ(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                    }
                    else if (contents.arg(0).is_int())
                    {
                        return builder.CreateICmpEQ(IntegerChild(0).ToLLVM(),IntegerChild(1).ToLLVM());
                    }
                    //Floating point comparison
                    else if (contents.arg(0).is_fpa())
                    {
                        FloatingChild(0).LLVMEq(FloatingChild(1));
                    }
                    else
                    {
                        UnsupportedSMTOpException("= comparison with unsupported child type", contents);
                    }
                case Z3_OP_DISTINCT:
                    if (contents.num_args() < 2)
                    {
                        throw UnsupportedSMTOpException("distinct comparison with less than 2 children", contents);
                    }
                    else if (contents.num_args() == 2)
                    {
                        if (contents.arg(0).is_bool())
                        {
                            return builder.CreateICmpNE(BooleanChild(0).ToLLVM(),BooleanChild(1).ToLLVM());
                        }
                        else if (contents.arg(0).is_bv())
                        {
                            return builder.CreateICmpNE(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                        }
                        else if (contents.arg(0).is_int())
                        {
                            return builder.CreateICmpNE(IntegerChild(0).ToLLVM(),IntegerChild(1).ToLLVM());
                        }
                        //Floating point comparison
                        else if (contents.arg(0).is_fpa())
                        {
                            return FloatingChild(0).LLVMNE(FloatingChild(1));
                        }
                        else
                        {
                            UnsupportedSMTOpException("distinct comparison with unsupported child type", contents);
                        }
                    }
                    else
                    {
                        //Check pairwise inequality for all pairs
                        throw NotImplementedException();
                    }
                default:
                    throw UnsupportedSMTOpException("boolean operation", contents);
            }
        }
    }

    APInt BooleanNode::LargestIntegerConstant()
    {
        //Boolean constants and variables don't contribute (i.e. 0)
        if (IsVariable() || IsConstant())
        {
            return APInt();
        }
        //Expressions (TODO: assumes only integer constraints in children)
        else if (Op() == Z3_OP_NOT)
        {
            return BooleanChild(0).LargestIntegerConstant();
        }
        else if (Op() == Z3_OP_AND || Op() == Z3_OP_OR || Op() == Z3_OP_XOR || Op() == Z3_OP_ITE || (Op() == Z3_OP_DISTINCT && contents.arg(0).is_bool()))
        {
            //Note: ITE always has exactly 3 arguments
            APInt val = BooleanChild(0).LargestIntegerConstant();
            for (int i = 1; i < contents.num_args(); i++)
            {
                val = APMax(val,BooleanChild(i).LargestIntegerConstant());
            }
            return val;
        }
        else if (Op() == Z3_OP_IMPLIES || (Op() == Z3_OP_EQ && contents.arg(0).is_bool()))
        {
            return APMax(BooleanChild(0).LargestIntegerConstant(),BooleanChild(1).LargestIntegerConstant());
        }
        else if (Op() == Z3_OP_LE || Op() == Z3_OP_LT || Op() == Z3_OP_GE || Op() == Z3_OP_GT || (Op() == Z3_OP_EQ && contents.arg(0).is_int()))
        {
            return APMax(IntegerChild(0).LargestIntegerConstant(),IntegerChild(1).LargestIntegerConstant());
        }
        else if (Op() == Z3_OP_DISTINCT && contents.arg(0).is_bool())
        {
            APInt val = IntegerChild(0).LargestIntegerConstant();
            for (int i = 1; i < contents.num_args(); i++)
            {
                val = APMax(val,IntegerChild(i).LargestIntegerConstant());
            }
            return val;
        }
        else
        {
            throw UnsupportedSMTOpException("largest constant computation with non-integer elements", contents);
        }
    }
    APInt BooleanNode::AbstractSingle(APInt assumption)
    {
        //Boolean constants and variables don't contribute (i.e. 0)
        if (IsVariable() || IsConstant())
        {
            return APInt();
        }
        //Expressions (TODO: assumes only integer constraints in children)
        else if (Op() == Z3_OP_NOT)
        {
            return BooleanChild(0).AbstractSingle(assumption);
        }
        else if (Op() == Z3_OP_AND || Op() == Z3_OP_OR || Op() == Z3_OP_XOR || Op() == Z3_OP_ITE || (Op() == Z3_OP_DISTINCT && contents.arg(0).is_bool()))
        {
            //Note: ITE always has exactly 3 arguments
            APInt val = BooleanChild(0).AbstractSingle(assumption);
            for (int i = 1; i < contents.num_args(); i++)
            {
                val = APMax(val,BooleanChild(i).AbstractSingle(assumption));
            }
            return val;
        }
        else if (Op() == Z3_OP_IMPLIES || (Op() == Z3_OP_EQ && contents.arg(0).is_bool()))
        {
            return APMax(BooleanChild(0).AbstractSingle(assumption),BooleanChild(1).AbstractSingle(assumption));
        }
        else if (Op() == Z3_OP_LE || Op() == Z3_OP_LT || Op() == Z3_OP_GE || Op() == Z3_OP_GT || (Op() == Z3_OP_EQ && contents.arg(0).is_int()))
        {
            return APMax(IntegerChild(0).AbstractSingle(assumption),IntegerChild(1).AbstractSingle(assumption));
        }
        else if (Op() == Z3_OP_DISTINCT && contents.arg(0).is_bool())
        {
            APInt val = IntegerChild(0).AbstractSingle(assumption);
            for (int i = 1; i < contents.num_args(); i++)
            {
                val = APMax(val,IntegerChild(i).AbstractSingle(assumption));
            }
            return val;
        }
        else
        {
            throw UnsupportedSMTOpException("largest constant computation with non-integer elements", contents);
        }
    }
    expr BooleanNode::ToSMT(unsigned width, std::map<std::string, expr> svariables)
    {
        if (IsVariable())
        {
            return svariables.at(contents.to_string());
        }
        else if (IsConstant())
        {
            return scx.bool_val(contents.bool_value()==Z3_L_TRUE);
        }
        else //Expression case
        {
            //Never used, but has to be initialized
            expr temp = scx.bool_val(true);
            expr left = scx.bool_val(true);
            expr right = scx.bool_val(true);
            switch (Op())
            {
                //Boolean only operations
                case Z3_OP_NOT:
                    return !BooleanChild(0).ToSMT(width,svariables);
                case Z3_OP_AND:
                    temp = BooleanChild(0).ToSMT(width, svariables);
                    for (int i = 1; i < contents.num_args(); i++)
                    {
                        temp = temp && BooleanChild(i).ToSMT(width, svariables);
                    }
                    return temp;
                case Z3_OP_OR:
                    temp = BooleanChild(0).ToSMT(width, svariables);
                    for (int i = 1; i < contents.num_args(); i++)
                    {
                        temp = temp || BooleanChild(i).ToSMT(width, svariables);
                    }
                    return temp;
                case Z3_OP_XOR:
                    temp = BooleanChild(0).ToSMT(width, svariables);
                    for (int i = 1; i < contents.num_args(); i++)
                    {
                        temp = temp ^ BooleanChild(i).ToSMT(width, svariables);
                    }
                    return temp;
                case Z3_OP_IMPLIES:
                    return implies(BooleanChild(0).ToSMT(width,svariables),BooleanChild(1).ToSMT(width,svariables));
                case Z3_OP_ITE:
                    return ite(BooleanChild(0).ToSMT(width,svariables),BooleanChild(1).ToSMT(width,svariables),BooleanChild(2).ToSMT(width,svariables));
                //Integer comparisons
                case Z3_OP_LE:
                    return IntegerChild(0).ToSMT(width,svariables) <= IntegerChild(1).ToSMT(width,svariables);
                case Z3_OP_LT:
                    return IntegerChild(0).ToSMT(width,svariables) < IntegerChild(1).ToSMT(width,svariables);
                case Z3_OP_GE:
                    return IntegerChild(0).ToSMT(width,svariables) >= IntegerChild(1).ToSMT(width,svariables);
                case Z3_OP_GT:
                    return IntegerChild(0).ToSMT(width,svariables) > IntegerChild(1).ToSMT(width,svariables);
                //equal and distinct comparisons (children can be any sort)
                case Z3_OP_EQ:
                    //Z3 parser converts = with more than 2 children into pairwise checks
                    assert(contents.num_args()==2);
                    //Boolean, bitvector, and integer are all integer (bitwise) comparison
                    if (contents.arg(0).is_bool())
                    {
                        return BooleanChild(0).ToSMT(width,svariables) == BooleanChild(1).ToSMT(width,svariables);
                    }
                    else if (contents.arg(0).is_int())
                    {
                        return IntegerChild(0).ToSMT(width,svariables) == IntegerChild(1).ToSMT(width,svariables);
                    }
                    else
                    {
                        UnsupportedSMTOpException("= comparison with unsupported child type", contents);
                    }
                case Z3_OP_DISTINCT:
                    if (contents.num_args() < 2)
                    {
                        throw UnsupportedSMTOpException("distinct comparison with less than 2 children", contents);
                    }
                    else if (contents.num_args() == 2)
                    {
                        if (contents.arg(0).is_bool())
                        {
                            return BooleanChild(0).ToSMT(width,svariables) != BooleanChild(1).ToSMT(width,svariables);
                        }
                        else if (contents.arg(0).is_int())
                        {
                            return IntegerChild(0).ToSMT(width,svariables) != IntegerChild(1).ToSMT(width,svariables);
                        }
                        else
                        {
                            UnsupportedSMTOpException("= comparison with unsupported child type", contents);
                        }
                    }
                    else
                    {
                        //Check pairwise inequality for all pairs
                        throw NotImplementedException();
                    }
                default:
                    throw UnsupportedSMTOpException("boolean operation", contents);
            }
        }
    }


    //==========================BitvectorNode==================================


    BitvectorNode::BitvectorNode(context& t_scx, LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, unsigned t_integer_width, const std::map<std::string, Value*>& t_variables, expr t_contents) : SMTNode(t_scx, t_lcx, t_lmodule, t_builder, t_integer_width, t_variables, t_contents)
    {
        //Sanity check for translation from Z3 expresssions
        assert(contents.is_bv());
    }

    //TODO: fill in this function
    Value * BitvectorNode::ToLLVM()
    {
        return ConstantInt::get(IntegerType::get(lcx,Width()), 0);
    }

    APInt BitvectorNode::LargestIntegerConstant()
    {
        throw UnsupportedSMTOpException("largest constant computation on bitvector value", contents);
    }
    APInt BitvectorNode::AbstractSingle(APInt assumption)
    {
        throw UnsupportedSMTOpException("abstract interpretation on bitvector value", contents);
    }
    expr BitvectorNode::ToSMT(unsigned width, std::map<std::string, expr> svariables)
    {
        throw UnsupportedSMTOpException("converstion to smt for bitvector value", contents);
    }


    //===========================FloatingNode==================================

    Type* FloatingNode::ToFloatingType(LLVMContext& lcx, std::string name, unsigned width)
    {
        switch (width)
        {
            case 16:
                return Type::getHalfTy(lcx);
            case 32:
                return Type::getFloatTy(lcx);
            case 64:
                return Type::getDoubleTy(lcx);
            case 128:
                return Type::getFP128Ty(lcx);
            default:
                throw UnsupportedSMTTypeException("Floating point type with width "+std::to_string(width),name);
        }
    }

    const std::map<Z3_decl_kind, int> FloatingNode::class_flags =  
    {
        {Z3_OP_FPA_IS_NAN,        3},   //0000000011 = signalging nan, quiet nan
        {Z3_OP_FPA_IS_INF,        516}, //1000000100 = negative infinity, positive infinity
        {Z3_OP_FPA_IS_ZERO,       96},  //0001100000 = negative zero, positive zero
        {Z3_OP_FPA_IS_NORMAL,     264}, //0100001000 = negative normal, positive normal
        {Z3_OP_FPA_IS_SUBNORMAL,  144}, //0010010000 = negative subnormal, positive subnormal
        {Z3_OP_FPA_IS_NEGATIVE,   60},  //0000111100 = neg infinity, neg normal, neg subnormal, neg zero
        {Z3_OP_FPA_IS_POSITIVE,   960}  //1111000000 = pos infinity, pos normal, pos subnormal, pos zero
    };

    //Returns an LLVM floating point class check expression
    Value * FloatingNode::LLVMClassCheck(Z3_decl_kind op)
    {
        std::vector<Value *> args;
        Value* val = ToLLVM();
        args.push_back(val);
        //Get constant int with the flags for the class check
        args.push_back(ConstantInt::get(IntegerType::get(lcx,32),class_flags.at(op)));
        //Get intrinsic function for class check
        Function * fun = Intrinsic::getDeclaration(lmodule, Function::lookupIntrinsicID("llvm.is.fpclass"), val->getType());
        return builder.CreateCall(fun,args);
    }

    //Returns an LLVM not equal comparison
    //Other must reference the same context and builder as this object
    Value * FloatingNode::LLVMNE(FloatingNode other)
    {
        //Context and builder should be the same for both objects
        assert(&lcx == &other.lcx);
        assert(&builder == &other.builder);

        IntegerType * iType = IntegerType::get(lcx,Width());
        Value* lb = builder.CreateBitCast(ToLLVM(),iType);
        Value* rb = builder.CreateBitCast(other.ToLLVM(),iType);

        //Not both NAN or different bits
        return builder.CreateOr(builder.CreateNot(builder.CreateAnd(LLVMClassCheck(Z3_OP_FPA_IS_NAN), other.LLVMClassCheck(Z3_OP_FPA_IS_NAN))), builder.CreateICmpNE(lb, rb));
    }

    //Returns an LLVM equal comparison
    //Other must reference the same context and builder as this object
    Value * FloatingNode::LLVMEq(FloatingNode other)
    {
        //Context and builder should be the same for both objects
        assert(&lcx == &other.lcx);
        assert(&builder == &other.builder);

        IntegerType * iType = IntegerType::get(lcx,Width());
        Value* lb = builder.CreateBitCast(ToLLVM(),iType);
        Value* rb = builder.CreateBitCast(other.ToLLVM(),iType);
        //Both NAN or have the same bits
        return builder.CreateOr(builder.CreateAnd(LLVMClassCheck(Z3_OP_FPA_IS_NAN), other.LLVMClassCheck(Z3_OP_FPA_IS_NAN)), builder.CreateICmpEQ(lb,rb));
    }

    FloatingNode::FloatingNode(context& t_scx, LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, unsigned t_integer_width, const std::map<std::string, Value*>& t_variables, expr t_contents) : SMTNode(t_scx, t_lcx, t_lmodule, t_builder, t_integer_width, t_variables, t_contents)
    {
        //Sanity check for translation from Z3 expresssions
        assert(contents.is_fpa());
    }

    //TODO: fill in this function
    Value * FloatingNode::ToLLVM()
    {
        return ConstantFP::getNaN(FloatingNode::ToFloatingType(lcx, contents.to_string(), Width()));
    }

    APInt FloatingNode::LargestIntegerConstant()
    {
        throw UnsupportedSMTOpException("largest constant computation on floating value", contents);
    }
    APInt FloatingNode::AbstractSingle(APInt assumption)
    {
        throw UnsupportedSMTOpException("abstract interpretation on floating value", contents);
    }
    expr FloatingNode::ToSMT(unsigned width, std::map<std::string, expr> svariables)
    {
        throw UnsupportedSMTOpException("converstion to smt for floating value", contents);
    }

    
}