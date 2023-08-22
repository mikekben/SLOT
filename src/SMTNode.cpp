#include "SMTNode.h"
#include "SLOTExceptions.h"


#ifndef LLMAPPING
#define LLMAPPING std::map<std::string, Value*>&
#endif

#define X_RM_VAR "variable rounding mode"
#define X_DISTINCT_CHILD "distinct comparison with less than 2 children"
#define X_DISTINCT_TYPE "distinct comparison with unsupported child type"
#define X_EQUAL_TYPE "= comparison with unsupported child type"
#define X_BOOLEAN_OP "boolean operation"
#define X_BV_OP "bitvector operation"
#define X_FP_TYPE "floating point type with width "
#define X_FP_CONVERT "to fp conversion"
#define X_FP_OP "floating point operation"


namespace SLOT
{
    //Syntax sugar for extracting children
    inline FloatingNode SMTNode::FloatingChild(expr cont) { return FloatingNode(lcx,lmodule,builder,variables,cont); }
    inline FloatingNode SMTNode::FloatingChild(int index) { return FloatingNode(lcx,lmodule,builder,variables,contents.arg(index)); }
    inline BitvectorNode SMTNode::BitvectorChild(expr cont) { return BitvectorNode(lcx,lmodule,builder,variables,cont); }
    inline BitvectorNode SMTNode::BitvectorChild(int index) { return BitvectorNode(lcx,lmodule,builder,variables,contents.arg(index)); }
    inline BooleanNode SMTNode::BooleanChild(expr cont) { return BooleanNode(lcx,lmodule,builder,variables,cont); }
    inline BooleanNode SMTNode::BooleanChild(int index) { return BooleanNode(lcx,lmodule,builder,variables,contents.arg(index)); }

    SMTNode::SMTNode(LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, const LLMAPPING& t_variables, expr t_contents) : lcx(t_lcx), lmodule(t_lmodule), builder(t_builder), variables(t_variables), contents(t_contents)
    {

    }

    //Returns LLVM rounding mode argument for constrained intrinsics
    MetadataAsValue* SMTNode::LLVMRoundingMode()
    {
        switch (RoundingMode())
        {
            case Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN:
                return MetadataAsValue::get(lcx, MDString::get(lcx, "round.tonearest"));
            case Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY:
                return MetadataAsValue::get(lcx, MDString::get(lcx, "round.tonearestaway"));
            case Z3_OP_FPA_RM_TOWARD_POSITIVE:         
                return MetadataAsValue::get(lcx, MDString::get(lcx, "round.upward"));
            case Z3_OP_FPA_RM_TOWARD_NEGATIVE:
                return MetadataAsValue::get(lcx, MDString::get(lcx, "round.downward"));
            case Z3_OP_FPA_RM_TOWARD_ZERO:
                return MetadataAsValue::get(lcx, MDString::get(lcx, "round.towardzero"));
            default:
                throw UnsupportedSMTOpException(X_RM_VAR, contents);
        }   
    }
    MetadataAsValue* SMTNode::LLVMException()
    {
        return MetadataAsValue::get(lcx, MDString::get(lcx, "fpexcept.ignore"));
    }

    //============================BooleanNode==================================


    BooleanNode::BooleanNode(LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, const LLMAPPING& t_variables, expr t_contents) : SMTNode(t_lcx, t_lmodule, t_builder, t_variables, t_contents)
    {
        //Sanity check for translation from Z3 expresssions
        assert(contents.is_bool());
    }

    Value* BooleanNode::ToLLVM()
    {
        if (IsVariable())
        {
            return variables.at(StrippedName());
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
                    assert(contents.num_args()==1);
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
                    assert(contents.num_args()==2);
                    return builder.CreateOr(builder.CreateNot(BooleanChild(0).ToLLVM()),BooleanChild(1).ToLLVM());
                case Z3_OP_ITE:
                    assert(contents.num_args()==3);
                    return builder.CreateSelect(BooleanChild(0).ToLLVM(),BooleanChild(1).ToLLVM(),BooleanChild(2).ToLLVM());
                //Bitvector comparisons
                case Z3_OP_SLEQ:
                    assert(contents.num_args()==2);
                    return builder.CreateICmpSLE(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                case Z3_OP_SGEQ:
                    assert(contents.num_args()==2);
                    return builder.CreateICmpSGE(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                case Z3_OP_SLT:
                    assert(contents.num_args()==2);
                    return builder.CreateICmpSLT(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                case Z3_OP_SGT:
                    assert(contents.num_args()==2);
                    return builder.CreateICmpSGT(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                case Z3_OP_ULEQ:
                    assert(contents.num_args()==2);
                    return builder.CreateICmpULE(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                case Z3_OP_UGEQ:
                    assert(contents.num_args()==2);
                    return builder.CreateICmpUGE(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                case Z3_OP_ULT:
                    assert(contents.num_args()==2);
                    return builder.CreateICmpULT(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                case Z3_OP_UGT:
                    assert(contents.num_args()==2);
                    return builder.CreateICmpUGT(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                //Floating comparisons. All comparisons are ordered
                //(SMT LIB says comparison is false if either argument is NAN)
                case Z3_OP_FPA_EQ:
                    assert(contents.num_args()==2);
                    return builder.CreateFCmpOEQ(FloatingChild(0).ToLLVM(), FloatingChild(1).ToLLVM());
                case Z3_OP_FPA_LT:
                    assert(contents.num_args()==2);
                    return builder.CreateFCmpOLT(FloatingChild(0).ToLLVM(), FloatingChild(1).ToLLVM());
                case Z3_OP_FPA_GT:
                    assert(contents.num_args()==2);
                    return builder.CreateFCmpOGT(FloatingChild(0).ToLLVM(), FloatingChild(1).ToLLVM());
                case Z3_OP_FPA_LE:
                    assert(contents.num_args()==2);
                    return builder.CreateFCmpOLE(FloatingChild(0).ToLLVM(), FloatingChild(1).ToLLVM());
                case Z3_OP_FPA_GE:
                    assert(contents.num_args()==2);
                    return builder.CreateFCmpOGE(FloatingChild(0).ToLLVM(), FloatingChild(1).ToLLVM());
                //Floating class checks
                case Z3_OP_FPA_IS_NAN: 
                case Z3_OP_FPA_IS_INF: 
                case Z3_OP_FPA_IS_ZERO: 
                case Z3_OP_FPA_IS_NORMAL: 
                case Z3_OP_FPA_IS_SUBNORMAL: 
                case Z3_OP_FPA_IS_NEGATIVE: 
                case Z3_OP_FPA_IS_POSITIVE:
                    assert(contents.num_args()==1);
                    return FloatingChild(0).LLVMClassCheck(Op());
                //equal and distinct comparisons (children can be any sort)
                case Z3_OP_EQ:
                    //Z3 parser converts = with more than 2 children into pairwise checks
                    assert(contents.num_args()==2);
                    if (contents.arg(0).is_bool())
                    {
                        return builder.CreateICmpEQ(BooleanChild(0).ToLLVM(),BooleanChild(1).ToLLVM());
                    }
                    else if (contents.arg(0).is_bv())
                    {
                        return builder.CreateICmpEQ(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                    }
                    else if (contents.arg(0).is_fpa())
                    {
                        return FloatingChild(0).LLVMEq(FloatingChild(1));
                    }
                    else
                    {
                        UnsupportedSMTOpException(X_EQUAL_TYPE, contents);
                    }
                case Z3_OP_DISTINCT:
                    if (contents.num_args() < 2)
                    {
                        throw UnsupportedSMTOpException(X_DISTINCT_CHILD, contents);
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
                        //Floating point comparison
                        else if (contents.arg(0).is_fpa())
                        {
                            return FloatingChild(0).LLVMNE(FloatingChild(1));
                        }
                        else
                        {
                            UnsupportedSMTOpException(X_DISTINCT_TYPE, contents);
                        }
                    }
                    else
                    {
                        //Check pairwise inequality for all pairs
                        Value* temp = 0; //  = ConstantInt::getTrue(*TheContext);
                        Value* v = 0;
                        for (int i = 0; i < contents.num_args(); i++)
                        {
                            for (int j = i+1; j < contents.num_args(); j++)
                            {
                                if (contents.arg(0).is_bool())
                                {
                                    v = builder.CreateICmpNE(BooleanChild(i).ToLLVM(), BooleanChild(j).ToLLVM());
                                }
                                else if (contents.arg(0).is_bv())
                                {
                                    v = builder.CreateICmpNE(BitvectorChild(i).ToLLVM(),BitvectorChild(j).ToLLVM());
                                }
                                else if (contents.arg(0).is_fpa())
                                {
                                    v = FloatingChild(i).LLVMNE(FloatingChild(j));
                                }
                                else
                                {
                                    UnsupportedSMTOpException(X_DISTINCT_TYPE, contents);
                                }
                                //Handle first time through loop correctly
                                temp = temp ? builder.CreateAnd(temp, v) : v;
                            }
                        }
                        return temp;
                    }
                default:
                    throw UnsupportedSMTOpException(X_BOOLEAN_OP, contents);
            }
        }
    }



    //==========================BitvectorNode==================================

    
    Value* BitvectorNode::LlURem(IRBuilder<>& builder, Value * left, Value * right)
    {
        return builder.CreateSelect(builder.CreateICmpEQ(right,ConstantInt::get(right->getType(), 0)), left, builder.CreateURem(left, right));
    }


    BitvectorNode::BitvectorNode(LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, const LLMAPPING& t_variables, expr t_contents) : SMTNode(t_lcx, t_lmodule, t_builder, t_variables, t_contents)
    {
        //Sanity check for translation from Z3 expresssions
        assert(contents.is_bv());
    }

    //TODO: fill in this function
    Value * BitvectorNode::ToLLVM()
    {
        if (IsVariable())
        {
            return variables.at(StrippedName());
        }
        else if (IsConstant())
        {
            // Either binary or hex representation for constants in SMT LIB
            assert(contents.to_string()[0] == '#' && (contents.to_string()[1] == 'b' || contents.to_string()[1] == 'x'));
            bool isBinary = contents.to_string()[1]=='b';
            return ConstantInt::get(IntegerType::get(lcx, Width()), contents.to_string().substr(2), isBinary?2:16);
        }
        else //Expression case
        {
            Value * one = ConstantInt::get(IntegerType::get(lcx, Width()), 1);
            Value * mone = builder.CreateNeg(one); //ConstantInt::get(IntegerType::get(lcx, Width()), -1);
            context c;
            Function * fun;
            std::vector<Value *> args;
            Value *temp, *u, *sel0, *sel1, *sel2;
            IntegerType *oldTp, *newTp, *ity;
            int oldWidth, times;
            switch(Op())
            {
                case Z3_OP_ITE:
                    assert(contents.num_args()==3);
                    return builder.CreateSelect(BooleanChild(0).ToLLVM(),BitvectorChild(1).ToLLVM(), BitvectorChild(2).ToLLVM());
                case Z3_OP_FPA_TO_UBV:
                    assert(contents.num_args()==2); //has rounding mode

                    args.push_back(FloatingChild(1).ToLLVM());
                    //Round according to rounding mode and then convert to unsigned bv
                    switch (RoundingMode())
                    {
                        case Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN:
                            fun = Intrinsic::getDeclaration(lmodule, Intrinsic::roundeven, FloatingNode::ToFloatingType(lcx, contents.to_string(), Width()));
                            break;
                        case Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY:
                            fun = Intrinsic::getDeclaration(lmodule, Intrinsic::lround, FloatingNode::ToFloatingType(lcx, contents.to_string(), Width()));
                            break;
                        case Z3_OP_FPA_RM_TOWARD_POSITIVE:         
                            fun = Intrinsic::getDeclaration(lmodule, Intrinsic::ceil, FloatingNode::ToFloatingType(lcx, contents.to_string(), Width()));
                            break;
                        case Z3_OP_FPA_RM_TOWARD_NEGATIVE:
                            fun = Intrinsic::getDeclaration(lmodule, Intrinsic::floor, FloatingNode::ToFloatingType(lcx, contents.to_string(), Width()));
                            break;
                        case Z3_OP_FPA_RM_TOWARD_ZERO:
                            //Default behavior of llvm fptoui
                            return builder.CreateFPToUI(FloatingChild(1).ToLLVM(), IntegerType::get(lcx, Width()));
                        default:
                            throw UnsupportedSMTOpException(X_RM_VAR, contents);
                    }
                    return builder.CreateFPToUI(builder.CreateCall(fun,args), IntegerType::get(lcx, Width()));
                case Z3_OP_FPA_TO_SBV:
                    assert(contents.num_args()==2); //has rounding mode

                    args.push_back(FloatingChild(1).ToLLVM());
                    //Round according to rounding mode and then convert to signed bv
                    switch (RoundingMode())
                    {
                        case Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN:
                            fun = Intrinsic::getDeclaration(lmodule, Intrinsic::roundeven, FloatingNode::ToFloatingType(lcx, contents.to_string(), Width()));
                            break;
                        case Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY:
                            fun = Intrinsic::getDeclaration(lmodule, Intrinsic::lround, FloatingNode::ToFloatingType(lcx, contents.to_string(), Width()));
                            break;
                        case Z3_OP_FPA_RM_TOWARD_POSITIVE:         
                            fun = Intrinsic::getDeclaration(lmodule, Intrinsic::ceil, FloatingNode::ToFloatingType(lcx, contents.to_string(), Width()));
                            break;
                        case Z3_OP_FPA_RM_TOWARD_NEGATIVE:
                            fun = Intrinsic::getDeclaration(lmodule, Intrinsic::floor, FloatingNode::ToFloatingType(lcx, contents.to_string(), Width()));
                            break;
                        case Z3_OP_FPA_RM_TOWARD_ZERO:
                            //Default behavior of llvm fptosi
                            return builder.CreateFPToSI(FloatingChild(1).ToLLVM(), IntegerType::get(lcx, Width()));
                        default:
                            throw UnsupportedSMTOpException(X_RM_VAR, contents);
                    }
                    return builder.CreateFPToSI(builder.CreateCall(fun,args), IntegerType::get(lcx, Width()));
                case Z3_OP_BNEG:
                    assert(contents.num_args()==1);
                    return builder.CreateSub(Zero(),BitvectorChild(0).ToLLVM());
                case Z3_OP_BADD:
                    assert(contents.num_args()==2);
                    return builder.CreateAdd(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                case Z3_OP_BSUB:
                    assert(contents.num_args()==2);
                    return builder.CreateSub(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                case Z3_OP_BMUL:
                    assert(contents.num_args()==2);
                    return builder.CreateMul(BitvectorChild(0).ToLLVM(),BitvectorChild(1).ToLLVM());
                case Z3_OP_BSDIV:
                    assert(contents.num_args()==2);
                    return builder.CreateSelect(BitvectorChild(1).IsZero(), builder.CreateSelect(BitvectorChild(0).IsNegative(), one, mone), builder.CreateSDiv(BitvectorChild(0).ToLLVM(), BitvectorChild(1).ToLLVM()));
                case Z3_OP_BUDIV:
                    assert(contents.num_args()==2);
                    return builder.CreateSelect(BitvectorChild(1).IsZero(), mone, builder.CreateUDiv(BitvectorChild(0).ToLLVM(), BitvectorChild(1).ToLLVM()));
                case Z3_OP_BSREM:
                    assert(contents.num_args()==2);
                    return builder.CreateSelect(BitvectorChild(1).IsZero(), BitvectorChild(0).ToLLVM(), builder.CreateSRem(BitvectorChild(0).ToLLVM(), BitvectorChild(1).ToLLVM()));
                case Z3_OP_BUREM:
                    assert(contents.num_args()==2);
                    return BitvectorNode::LlURem(builder, BitvectorChild(0).ToLLVM(), BitvectorChild(1).ToLLVM());
                case Z3_OP_BSMOD:
                    assert(contents.num_args()==2);
                    u = BitvectorNode::LlURem(builder, builder.CreateSelect(BitvectorChild(0).IsNegative(), builder.CreateSub(Zero(), BitvectorChild(0).ToLLVM()), BitvectorChild(0).ToLLVM()), builder.CreateSelect(BitvectorChild(1).IsNegative(), builder.CreateSub(Zero(), BitvectorChild(1).ToLLVM()), BitvectorChild(1).ToLLVM()));
                    sel0 = builder.CreateSelect(builder.CreateAnd(BitvectorChild(0).IsPositive(),BitvectorChild(1).IsNegative()), builder.CreateAdd(u, BitvectorChild(1).ToLLVM()), builder.CreateSub(Zero(), u));
                    sel1 = builder.CreateSelect(builder.CreateAnd(BitvectorChild(0).IsNegative(),BitvectorChild(1).IsPositive()), builder.CreateAdd(builder.CreateSub(Zero(),u), BitvectorChild(1).ToLLVM()), sel0);
                    sel2 = builder.CreateSelect(builder.CreateAnd(BitvectorChild(0).IsPositive(),BitvectorChild(1).IsPositive()), u, sel1);
                    return builder.CreateSelect(builder.CreateICmpEQ(u, Zero()), u, sel2);
                case Z3_OP_BAND:
                    temp = BitvectorChild(0).ToLLVM();
                    for (int i = 1; i < contents.num_args(); i++)
                    {
                        temp = builder.CreateAnd(temp,BitvectorChild(i).ToLLVM());
                    }
                    return temp;
                case Z3_OP_BOR:
                    temp = BitvectorChild(0).ToLLVM();
                    for (int i = 1; i < contents.num_args(); i++)
                    {
                        temp = builder.CreateOr(temp,BitvectorChild(i).ToLLVM());
                    }
                    return temp;
                case Z3_OP_BNOT:
                    return builder.CreateNot(BitvectorChild(0).ToLLVM());
                case Z3_OP_BXOR:
                    assert(contents.num_args() > 1);
                    temp = BitvectorChild(0).ToLLVM();
                    for (int i = 1; i < contents.num_args(); i++)
                    {
                        temp = builder.CreateXor(temp,BitvectorChild(i).ToLLVM());
                    }
                    return temp;
                case Z3_OP_BNAND:
                    assert(contents.num_args()==2);
                    return builder.CreateNot(builder.CreateAnd(BitvectorChild(0).ToLLVM(), BitvectorChild(1).ToLLVM()));
                case Z3_OP_BNOR:
                    assert(contents.num_args()==2);
                    return builder.CreateNot(builder.CreateOr(BitvectorChild(0).ToLLVM(), BitvectorChild(1).ToLLVM()));
                case Z3_OP_BXNOR:
                    assert(contents.num_args()==2);
                    return builder.CreateNot(builder.CreateXor(BitvectorChild(0).ToLLVM(), BitvectorChild(1).ToLLVM()));
                case Z3_OP_CONCAT:
                    assert(contents.num_args()==2);
                    sel0 = builder.CreateZExt(BitvectorChild(0).ToLLVM(), IntegerType::get(lcx, Width()));
                    sel1 = builder.CreateZExt(BitvectorChild(1).ToLLVM(), IntegerType::get(lcx, Width()));
                    sel2 = builder.CreateShl(sel0, ConstantInt::get(IntegerType::get(lcx, Width()), BitvectorChild(1).Width()));
                    return builder.CreateOr(sel1, sel2);
                case Z3_OP_SIGN_EXT:
                    assert(contents.num_args()==1);
                    return builder.CreateSExt(BitvectorChild(0).ToLLVM(), IntegerType::get(lcx, Width()));
                case Z3_OP_ZERO_EXT:
                    assert(contents.num_args()==1);
                    return builder.CreateZExt(BitvectorChild(0).ToLLVM(), IntegerType::get(lcx, Width()));
                case Z3_OP_EXTRACT:
                    assert(contents.num_args()==1);
                    oldTp = IntegerType::get(lcx, BitvectorChild(0).Width());
                    newTp = IntegerType::get(lcx, contents.hi() - contents.lo() + 1);
                    return builder.CreateTrunc(builder.CreateLShr(BitvectorChild(0).ToLLVM(), ConstantInt::get(oldTp, contents.lo())), newTp);
                case Z3_OP_REPEAT:
                    assert(contents.num_args()==1);
                    oldWidth = BitvectorChild(0).Width();
                    times = Width()/oldWidth;
                    assert(oldWidth*times == Width() && times > 0);
                    u = BitvectorChild(0).ToLLVM();
                    if (times==1)
                    {
                        return BitvectorChild(0).ToLLVM();
                    }
                    else
                    {
                        temp = builder.CreateZExt(BitvectorChild(0).ToLLVM(),IntegerType::get(lcx,Width()));
                        for (int i = 1; i < times; i++)
                        {
                            temp = builder.CreateOr(temp,builder.CreateShl(builder.CreateZExt(BitvectorChild(0).ToLLVM(),IntegerType::get(lcx,Width())), ConstantInt::get(IntegerType::get(lcx,Width()),i*oldWidth)));
                        }
                        return temp;
                    }
                case Z3_OP_BCOMP:
                    assert(contents.num_args()==2);
                    return builder.CreateICmpEQ(BitvectorChild(0).ToLLVM(), BitvectorChild(1).ToLLVM());
                case Z3_OP_BSHL:
                    assert(contents.num_args()==2);
                    newTp = IntegerType::get(lcx, BitvectorChild(0).Width());
                    return builder.CreateSelect(builder.CreateICmpUGE(BitvectorChild(1).ToLLVM(), ConstantInt::get(newTp,Width())), ConstantInt::get(newTp,0), builder.CreateShl(BitvectorChild(0).ToLLVM(), BitvectorChild(1).ToLLVM()));
                case Z3_OP_BLSHR:
                    assert(contents.num_args()==2);
                    newTp = IntegerType::get(lcx, BitvectorChild(0).Width());
                    return builder.CreateSelect(builder.CreateICmpUGE(BitvectorChild(1).ToLLVM(), ConstantInt::get(newTp,Width())), ConstantInt::get(newTp,0), builder.CreateLShr(BitvectorChild(0).ToLLVM(), BitvectorChild(1).ToLLVM()));
                case Z3_OP_BASHR:
                    assert(contents.num_args()==2);
                    newTp = IntegerType::get(lcx, BitvectorChild(0).Width());
                    temp = builder.CreateSelect(BitvectorChild(0).IsNegative(), mone, ConstantInt::get(newTp, 0));
                    return builder.CreateSelect(builder.CreateICmpUGE(BitvectorChild(1).ToLLVM(), ConstantInt::get(newTp,Width())), temp, builder.CreateAShr(BitvectorChild(0).ToLLVM(), BitvectorChild(1).ToLLVM()));
                case Z3_OP_ROTATE_LEFT:
                    assert(contents.num_args()==1);

                    ity = IntegerType::get(lcx, Width());
                    temp = BitvectorChild(0).ToLLVM();

                    args.push_back(temp);
                    args.push_back(temp);
                    args.push_back(ConstantInt::get(ity, Z3_get_decl_int_parameter(c, contents.decl(),0)%Width()));

                    fun = Intrinsic::getDeclaration(lmodule, Intrinsic::fshl, ity);
                    return builder.CreateCall(fun,args);
                case Z3_OP_ROTATE_RIGHT:
                    assert(contents.num_args()==1);

                    ity = IntegerType::get(lcx, Width());
                    temp = BitvectorChild(0).ToLLVM();

                    args.push_back(temp);
                    args.push_back(temp);
                    args.push_back(ConstantInt::get(ity, Z3_get_decl_int_parameter(c, contents.decl(),0)%Width()));

                    fun = Intrinsic::getDeclaration(lmodule, Intrinsic::fshr, ity);
                    return builder.CreateCall(fun,args);
                default:
                    throw UnsupportedSMTOpException(X_BV_OP, contents);
            }
        }
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
                throw UnsupportedTypeException(X_FP_TYPE+std::to_string(width),name);
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
        return builder.CreateAnd(builder.CreateNot(builder.CreateAnd(LLVMClassCheck(Z3_OP_FPA_IS_NAN), other.LLVMClassCheck(Z3_OP_FPA_IS_NAN))), builder.CreateICmpNE(lb, rb));
    }

    //Returns an LLVM equal comparison
    //Other must reference the same context and builder as this object
    Value * FloatingNode::LLVMEq(FloatingNode other)
    {
        // Context and builder should be the same for both objects
        assert(&lcx == &other.lcx);
        assert(&builder == &other.builder);

        IntegerType * iType = IntegerType::get(lcx,Width());
        Value* lb = builder.CreateBitCast(ToLLVM(),iType);
        Value* rb = builder.CreateBitCast(other.ToLLVM(),iType);

        //Both NAN or have the same bits
        return builder.CreateOr(builder.CreateAnd(LLVMClassCheck(Z3_OP_FPA_IS_NAN), other.LLVMClassCheck(Z3_OP_FPA_IS_NAN)), builder.CreateICmpEQ(lb,rb));
    }

    FloatingNode::FloatingNode(LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, const LLMAPPING& t_variables, expr t_contents) : SMTNode(t_lcx, t_lmodule, t_builder, t_variables, t_contents)
    {

        //Sanity check for translation from Z3 expresssions
        assert(contents.is_fpa());
    }

    //TODO: fill in this function
    Value * FloatingNode::ToLLVM()
    {
        if (IsVariable())
        {
            return variables.at(StrippedName());
        }
        //There are no floating point constants, all are constructed from bitvectors
        else //Expression case
        {
            Value *sign, *exp, *sig;
            std::vector<Value *> args;
            std::vector<Type *> types;
            Function *fun;
            MDNode *roundingModeNode;
            switch (Op())
            {
                case Z3_OP_ITE:
                    assert(contents.num_args()==3);
                    return builder.CreateSelect(BooleanChild(0).ToLLVM(), FloatingChild(1).ToLLVM(), FloatingChild(2).ToLLVM());
                case Z3_OP_FPA_TO_FP_UNSIGNED:
                    assert(contents.num_args()==2); // has rounding mode

                    if (IsRNE())
                    {
                        return builder.CreateUIToFP(BitvectorChild(1).ToLLVM(), FloatingType());
                    }
                    else
                    {
                        args.push_back(BitvectorChild(1).ToLLVM());
                        args.push_back(LLVMRoundingMode());
                        args.push_back(LLVMException());

                        types.push_back(FloatingType());
                        types.push_back(IntegerType::get(lcx, Width()));

                        fun = Intrinsic::getDeclaration(lmodule, Intrinsic::experimental_constrained_uitofp, types);
                        return builder.CreateCall(fun, args);
                    }
                case Z3_OP_FPA_TO_FP:
                    if (contents.num_args() == 1)
                    {
                        assert(contents.num_args()==1);
                        return builder.CreateBitCast(BitvectorChild(0).ToLLVM(), FloatingType());
                    }
                    else if (contents.arg(1).is_bv())
                    {
                        assert(contents.num_args()==2); // has rounding mode
                        
                        if (IsRNE())
                        {
                            return builder.CreateSIToFP(BitvectorChild(1).ToLLVM(), FloatingType());
                        }
                        else
                        {
                            args.push_back(BitvectorChild(1).ToLLVM());
                            args.push_back(LLVMRoundingMode());
                            args.push_back(LLVMException());

                            types.push_back(FloatingType());
                            types.push_back(IntegerType::get(lcx, Width()));
                            
                            fun = Intrinsic::getDeclaration(lmodule, Intrinsic::experimental_constrained_sitofp, types);
                            return builder.CreateCall(fun, args);
                        }
                    }
                    else if (contents.arg(1).is_fpa())
                    {
                        assert(contents.num_args()==2); // has rounding mode
                        //may be the same, extension, or truncation

                        //No width change; nothing necessary
                        if (Width() == FloatingChild(1).Width())
                        {
                            return FloatingChild(1).ToLLVM();
                        }
                        
                        //In each case, check whether operation is extending or truncating
                        if (IsRNE())
                        {
                            if (Width() > FloatingChild(1).Width())
                            {
                                return builder.CreateFPExt(FloatingChild(1).ToLLVM(),FloatingType());
                            }
                            else
                            {
                                return builder.CreateFPTrunc(FloatingChild(1).ToLLVM(),FloatingType());
                            }
                        }
                        else
                        {
                            args.push_back(FloatingChild(1).ToLLVM());
                            args.push_back(LLVMRoundingMode());
                            args.push_back(LLVMException());
                            if (Width() > FloatingChild(1).Width())
                            {
                                fun = Intrinsic::getDeclaration(lmodule, Intrinsic::experimental_constrained_fpext, FloatingType());
                            }
                            else
                            {
                                fun = Intrinsic::getDeclaration(lmodule, Intrinsic::experimental_constrained_fptrunc, FloatingType());
                            }
                            return builder.CreateCall(fun, args);
                        }
                    }
                    else { throw UnsupportedSMTOpException(X_FP_CONVERT, contents); }
                case Z3_OP_FPA_FP:
                    assert(contents.num_args()==3);
                    sign = builder.CreateShl(builder.CreateZExt(BitvectorChild(0).ToLLVM(), IntegerType::get(lcx,Width())), ConstantInt::get(IntegerType::get(lcx, Width()), Width()-1));
                    exp = builder.CreateShl(builder.CreateZExt(BitvectorChild(1).ToLLVM(), IntegerType::get(lcx,Width())), ConstantInt::get(IntegerType::get(lcx,Width()), SBits()-1));
                    sig = builder.CreateZExt(BitvectorChild(2).ToLLVM(), IntegerType::get(lcx,Width()));

                    return builder.CreateBitCast(builder.CreateOr(sign, builder.CreateOr(exp, sig)), FloatingType());
                case Z3_OP_FPA_ROUND_TO_INTEGRAL:
                    assert(contents.num_args()==2); //has rounding mode

                    args.push_back(FloatingChild(1).ToLLVM());
                    //Different LLVM rounding functions for each rounding mode
                    switch (RoundingMode())
                    {
                        case Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN:
                            fun = Intrinsic::getDeclaration(lmodule, Intrinsic::roundeven, FloatingType());
                            break;
                        case Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY:
                            fun = Intrinsic::getDeclaration(lmodule, Intrinsic::lround, FloatingType());
                            break;
                        case Z3_OP_FPA_RM_TOWARD_POSITIVE:         
                            fun = Intrinsic::getDeclaration(lmodule, Intrinsic::ceil, FloatingType());
                            break;
                        case Z3_OP_FPA_RM_TOWARD_NEGATIVE:
                            fun = Intrinsic::getDeclaration(lmodule, Intrinsic::floor, FloatingType());
                            break;
                        case Z3_OP_FPA_RM_TOWARD_ZERO:
                            fun = Intrinsic::getDeclaration(lmodule, Intrinsic::trunc, FloatingType());
                            break;
                        default:
                            throw UnsupportedSMTOpException(X_RM_VAR, contents);
                    }
                    return builder.CreateCall(fun,args);
                case Z3_OP_FPA_NAN:
                    assert(contents.num_args()==0);
                    return ConstantFP::getNaN(FloatingType());
                case Z3_OP_FPA_MINUS_INF:
                    assert(contents.num_args()==0);
                    return ConstantFP::getInfinity(FloatingType(), true);
                case Z3_OP_FPA_PLUS_INF:
                    assert(contents.num_args()==0);
                    return ConstantFP::getInfinity(FloatingType(), false);
                case Z3_OP_FPA_MINUS_ZERO:
                    assert(contents.num_args()==0);
                    return ConstantFP::getNegativeZero(FloatingType());
                case Z3_OP_FPA_PLUS_ZERO:
                    assert(contents.num_args()==0);
                    //there is no ConstantFP::getZero
                    return builder.CreateFNeg(ConstantFP::getNegativeZero(FloatingType()));
                case Z3_OP_FPA_ABS:
                    assert(contents.num_args()==1);
                    
                    args.push_back(FloatingChild(0).ToLLVM());
                    fun = Intrinsic::getDeclaration(lmodule, Intrinsic::fabs, FloatingType());
                    return builder.CreateCall(fun,args);
                case Z3_OP_FPA_NEG:
                    assert(contents.num_args()==1);
                    return builder.CreateFNeg(FloatingChild(0).ToLLVM());
                case Z3_OP_FPA_ADD:
                    assert(contents.num_args()==3); //has rounding mode
                    if (IsRNE())
                    {
                        return builder.CreateFAdd(FloatingChild(1).ToLLVM(), FloatingChild(2).ToLLVM());
                    }
                    else
                    {
                        args.push_back(FloatingChild(1).ToLLVM());
                        args.push_back(FloatingChild(2).ToLLVM());
                        args.push_back(LLVMRoundingMode());
                        args.push_back(LLVMException());
                        fun = Intrinsic::getDeclaration(lmodule, Intrinsic::experimental_constrained_fadd, FloatingType());
                        return builder.CreateCall(fun, args);
                    }
                case Z3_OP_FPA_SUB:
                    assert(contents.num_args()==3); //has rounding mode
                    if (IsRNE())
                    {
                        return builder.CreateFSub(FloatingChild(1).ToLLVM(), FloatingChild(2).ToLLVM());
                    }
                    else
                    {
                        args.push_back(FloatingChild(1).ToLLVM());
                        args.push_back(FloatingChild(2).ToLLVM());
                        args.push_back(LLVMRoundingMode());
                        args.push_back(LLVMException());
                        fun = Intrinsic::getDeclaration(lmodule, Intrinsic::experimental_constrained_fsub, FloatingType());
                        return builder.CreateCall(fun, args);
                    }
                case Z3_OP_FPA_MUL:
                    assert(contents.num_args()==3); //has rounding mode
                    if (IsRNE())
                    {
                        return builder.CreateFMul(FloatingChild(1).ToLLVM(), FloatingChild(2).ToLLVM());
                    }
                    else
                    {
                        args.push_back(FloatingChild(1).ToLLVM());
                        args.push_back(FloatingChild(2).ToLLVM());
                        args.push_back(LLVMRoundingMode());
                        args.push_back(LLVMException());
                        fun = Intrinsic::getDeclaration(lmodule, Intrinsic::experimental_constrained_fmul, FloatingType());
                        return builder.CreateCall(fun, args);
                    }
                case Z3_OP_FPA_DIV:
                    assert(contents.num_args()==3); //has rounding mode
                    if (IsRNE())
                    {
                        return builder.CreateFDiv(FloatingChild(1).ToLLVM(), FloatingChild(2).ToLLVM());
                    }
                    else
                    {
                        args.push_back(FloatingChild(1).ToLLVM());
                        args.push_back(FloatingChild(2).ToLLVM());
                        args.push_back(LLVMRoundingMode());
                        args.push_back(LLVMException());
                        fun = Intrinsic::getDeclaration(lmodule, Intrinsic::experimental_constrained_fdiv, FloatingType());
                        return builder.CreateCall(fun, args);
                    }
                case Z3_OP_FPA_REM:
                    assert(contents.num_args()==2);
                    return builder.CreateFRem(FloatingChild(0).ToLLVM(), FloatingChild(1).ToLLVM());
                case Z3_OP_FPA_FMA:
                    assert(contents.num_args()==4); //has rounding mode
                    args.push_back(FloatingChild(1).ToLLVM());
                    args.push_back(FloatingChild(2).ToLLVM());
                    args.push_back(FloatingChild(3).ToLLVM());

                    if (IsRNE())
                    {
                        fun = Intrinsic::getDeclaration(lmodule, Intrinsic::fma, FloatingType());
                    }
                    else
                    {
                        args.push_back(LLVMRoundingMode());
                        args.push_back(LLVMException());
                        fun = Intrinsic::getDeclaration(lmodule, Intrinsic::experimental_constrained_fma, FloatingType());
                    }
                    return builder.CreateCall(fun,args);
                case Z3_OP_FPA_SQRT:
                    assert(contents.num_args()==2); //has rounding mode
                    args.push_back(FloatingChild(1).ToLLVM());

                    if (IsRNE())
                    {
                        fun = Intrinsic::getDeclaration(lmodule, Intrinsic::sqrt, FloatingType());
                    }
                    else
                    {
                        args.push_back(LLVMRoundingMode());
                        args.push_back(LLVMException());
                        fun = Intrinsic::getDeclaration(lmodule, Intrinsic::experimental_constrained_sqrt, FloatingType());
                    }
                    return builder.CreateCall(fun,args);
                case Z3_OP_FPA_MIN:
                    assert(contents.num_args()==2);
                    args.push_back(FloatingChild(0).ToLLVM());
                    args.push_back(FloatingChild(1).ToLLVM());

                    fun = Intrinsic::getDeclaration(lmodule, Intrinsic::minnum, FloatingType());
                    return builder.CreateCall(fun,args);
                case Z3_OP_FPA_MAX:
                    assert(contents.num_args()==2);
                    args.push_back(FloatingChild(0).ToLLVM());
                    args.push_back(FloatingChild(1).ToLLVM());

                    fun = Intrinsic::getDeclaration(lmodule, Intrinsic::maxnum, FloatingType());
                    return builder.CreateCall(fun,args);
                default:
                    throw UnsupportedSMTOpException(X_FP_OP, contents);
            }
        }
    }
}