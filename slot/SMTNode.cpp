#include "SMTNode.h"
#include "SLOTExceptions.h"


#ifndef LLMAPPING
#define LLMAPPING std::map<std::string, Value*>&
#endif


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
                                    UnsupportedSMTOpException("distinct comparison with unsupported child type", contents);
                                }
                                //Handle first time through loop correctly
                                temp = temp ? builder.CreateAnd(temp, v) : v;
                            }
                        }
                        return temp;
                    }
                default:
                    throw UnsupportedSMTOpException("boolean operation", contents);
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
        if (Op() == Z3_OP_FPA_TO_UBV || Op() == Z3_OP_FPA_TO_SBV)
        {
            Z3_decl_kind k = contents.arg(0).decl().decl_kind();
            switch(k)
            {
                case Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY:
                case Z3_OP_FPA_RM_TOWARD_POSITIVE:
                case Z3_OP_FPA_RM_TOWARD_NEGATIVE:
                case Z3_OP_FPA_RM_TOWARD_ZERO:
                    throw UnsupportedSMTOpException("floating point rounding mode", contents);
                default:
                    break;
            }
        }
    }

    //TODO: fill in this function
    Value * BitvectorNode::ToLLVM()
    {
        if (IsVariable())
        {
            return variables.at(contents.to_string());
        }
        else if (IsConstant())
        {
            //Either binary or hex representation for constants in SMT LIB
            assert(contents.to_string()[0] == '#' && (contents.to_string()[1] == 'b' || contents.to_string()[1] == 'x'));
            bool isBinary = contents.to_string()[1]=='b';
            return ConstantInt::get(IntegerType::get(lcx, Width()), contents.to_string().substr(2), isBinary?2:16);
        }
        else //Expression case
        {
            Value * one = ConstantInt::get(IntegerType::get(lcx, Width()), 1);
            Value * mone = ConstantInt::get(IntegerType::get(lcx, Width()), -1);
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
                    assert(contents.num_args()==1);
                    return builder.CreateFPToUI(FloatingChild(1).ToLLVM(), IntegerType::get(lcx, Width()));
                case Z3_OP_FPA_TO_SBV:
                    assert(contents.num_args()==1);
                    return builder.CreateFPToSI(FloatingChild(1).ToLLVM(), IntegerType::get(lcx, Width()));
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
                    assert(contents.num_args()==2);
                    return builder.CreateAnd(BitvectorChild(0).ToLLVM(), BitvectorChild(1).ToLLVM());
                case Z3_OP_BOR:
                    assert(contents.num_args()==2);
                    return builder.CreateOr(BitvectorChild(0).ToLLVM(), BitvectorChild(1).ToLLVM());
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
                    temp = builder.CreateSelect(BitvectorChild(0).IsNegative(), ConstantInt::get(newTp,-1), ConstantInt::get(newTp, 0));
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
                    throw UnsupportedSMTOpException("bitvector operation", contents);
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
                throw UnsupportedTypeException("Floating point type with width "+std::to_string(width),name);
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

    FloatingNode::FloatingNode(LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, const LLMAPPING& t_variables, expr t_contents) : SMTNode(t_lcx, t_lmodule, t_builder, t_variables, t_contents)
    {
        //Sanity check for translation from Z3 expresssions
        assert(contents.is_fpa());

        //Check for unsupported rounding modes
        Z3_decl_kind k = contents.arg(0).decl().decl_kind();
        switch(k)
        {
            case Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY:
            case Z3_OP_FPA_RM_TOWARD_POSITIVE:
            case Z3_OP_FPA_RM_TOWARD_NEGATIVE:
            case Z3_OP_FPA_RM_TOWARD_ZERO:
                throw UnsupportedSMTOpException("floating point rounding mode", contents);
            default:
                break;
        }
    }

    //TODO: fill in this function
    Value * FloatingNode::ToLLVM()
    {
        if (IsVariable())
        {
            return variables.at(contents.to_string());
        }
        //There are no floating point constants, all are constructed from bitvectors
        else //Expression case
        {
            Value *sign, *exp, *sig;
            std::vector<Value *> args;
            Function * fun;
            switch(Op())
            {
                case Z3_OP_ITE:
                    assert(contents.num_args()==3);
                    return builder.CreateSelect(BooleanChild(0).ToLLVM(), FloatingChild(1).ToLLVM(), FloatingChild(2).ToLLVM());
                case Z3_OP_FPA_TO_FP_UNSIGNED:
                    assert(contents.num_args()==2); // has rounding mode
                    return builder.CreateUIToFP(BitvectorChild(1).ToLLVM(), FloatingType());
                case Z3_OP_FPA_TO_FP:
                    if (contents.num_args() == 1)
                    {
                        assert(contents.num_args()==1);
                        return builder.CreateBitCast(BitvectorChild(0).ToLLVM(), FloatingType());
                    }
                    else if (contents.arg(1).is_bv())
                    {
                        assert(contents.num_args()==2); // has rounding mode
                        return builder.CreateSIToFP(BitvectorChild(1).ToLLVM(), FloatingType());
                    }
                    else if (contents.arg(1).is_fpa())
                    {
                        assert(contents.num_args()==2); // has rounding mode
                        //may be the same, extension, or truncation

                        if (Width() == FloatingChild(1).Width())
                        {
                            return FloatingChild(1).ToLLVM();
                        }
                        else if (Width() > FloatingChild(1).Width())
                        {
                            return builder.CreateFPExt(FloatingChild(1).ToLLVM(),FloatingType());
                        }
                        else
                        {
                            return builder.CreateFPTrunc(FloatingChild(1).ToLLVM(),FloatingType());
                        }
                    }
                    else { throw UnsupportedSMTOpException("to fp conversion", contents); }
                case Z3_OP_FPA_FP:
                    assert(contents.num_args()==3);
                    sign = builder.CreateShl(builder.CreateZExt(BitvectorChild(0).ToLLVM(), IntegerType::get(lcx,Width())), ConstantInt::get(IntegerType::get(lcx, Width()), Width()-1));
                    exp = builder.CreateShl(builder.CreateZExt(BitvectorChild(1).ToLLVM(), IntegerType::get(lcx,Width())), ConstantInt::get(IntegerType::get(lcx,Width()), SBits()-1));
                    sig = builder.CreateZExt(BitvectorChild(2).ToLLVM(), IntegerType::get(lcx,Width()));

                    return builder.CreateBitCast(builder.CreateOr(sign, builder.CreateOr(exp, sig)), FloatingType());
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
                    return builder.CreateFAdd(FloatingChild(1).ToLLVM(), FloatingChild(2).ToLLVM());
                case Z3_OP_FPA_SUB:
                    assert(contents.num_args()==3); //has rounding mode
                    return builder.CreateFSub(FloatingChild(1).ToLLVM(), FloatingChild(2).ToLLVM());
                case Z3_OP_FPA_MUL:
                    assert(contents.num_args()==3); //has rounding mode
                    return builder.CreateFMul(FloatingChild(1).ToLLVM(), FloatingChild(2).ToLLVM());
                case Z3_OP_FPA_DIV:
                    assert(contents.num_args()==3); //has rounding mode
                    return builder.CreateFDiv(FloatingChild(1).ToLLVM(), FloatingChild(2).ToLLVM());
                case Z3_OP_FPA_REM:
                    assert(contents.num_args()==2);
                    return builder.CreateFRem(FloatingChild(0).ToLLVM(), FloatingChild(0).ToLLVM());
                case Z3_OP_FPA_FMA:
                    assert(contents.num_args()==4); //has rounding mode
                    args.push_back(FloatingChild(1).ToLLVM());
                    args.push_back(FloatingChild(2).ToLLVM());
                    args.push_back(FloatingChild(3).ToLLVM());

                    fun = Intrinsic::getDeclaration(lmodule, Intrinsic::fma, FloatingType());
                    return builder.CreateCall(fun,args);
                case Z3_OP_FPA_SQRT:
                    assert(contents.num_args()==2); //has rounding mode
                    args.push_back(FloatingChild(1).ToLLVM());

                    fun = Intrinsic::getDeclaration(lmodule, Intrinsic::sqrt, FloatingType());
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
                    throw UnsupportedSMTOpException("floating point operation", contents);
            }
        }
    }
}






/*
bool RealNode::IsComparison(expr expression) //static
    {
        Z3_decl_kind k = expression.decl().decl_kind();
        bool direct = (k == Z3_OP_LE || k == Z3_OP_LT || k == Z3_OP_GE || k == Z3_OP_GT);
        return expression.num_args() >= 1 && expression.arg(0).is_real() && (expression.is_eq() || expression.is_distinct() || direct);
    }

    RealNode::RealNode(context& t_scx, LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, unsigned t_integer_width, const std::map<std::string, Value*>& t_variables, expr t_contents) : SMTNode(t_scx, t_lcx, t_lmodule, t_builder, t_integer_width, t_variables, t_contents)
    {
        //Sanity check for translation from Z3 expresssions
        assert(contents.is_real());
    }

    Value* RealNode::ToLLVM()
    {
        throw UnsupportedSMTOpException("real number conversion to LLVM", contents);
    }
    APInt RealNode::LargestIntegerConstant()
    {
        throw UnsupportedSMTOpException("real number LIC", contents);
    }
    expr RealNode::ToSMT(unsigned width, std::map<std::string, expr> svariables, solver* sol)
    {
        throw UnsupportedSMTOpException("real number ToSMT", contents);
    }
    PAIR RealNode::LargestPreciseConstant()
    {
        if (IsVariable())
        {
            return {APInt(), 0};
        }
        else if (IsConstant())
        {
            //Handle negative constants
            std::string str = contents.get_decimal_string(INT_MAX);
            if (str[0]=='(' && str[1]=='-')
            {
                str.erase(0,1);
                str.erase(1,1);
                str.erase(str.length()-1,1);
            }
            unsigned decimals = str.length();
            //If a decimal, get the precision and the size seperately
            if (str.find('.')>=0)
            {
                decimals--; //One less digit, since the . doesn't count
                str = str.substr(0,str.find('.'));
            }

            //Length in base 10 * 4 (log_2(10) + 1) to guarantee enough width
            return {APInt(str.length()*4, str, 10).abs()+1, decimals};
        }
        //Expressions (TODO: assumes only real constraints in children)
        else if (Op() == Z3_OP_ITE)
        {
            PAIR cond = BooleanChild(0).LargestPreciseConstant();
            PAIR left = RealChild(1).LargestPreciseConstant();
            PAIR right = RealChild(2).LargestPreciseConstant();
            return PairMax(cond,PairMax(left,right));
        }
        else if (Op() == Z3_OP_UMINUS)
        {
            return RealChild(0).LargestPreciseConstant();
        }
        else //Binary real expressions
        {
            return PairMax(RealChild(0).LargestPreciseConstant(),RealChild(1).LargestPreciseConstant());
        }
    }
    APInt RealNode::AbstractSingle(APInt assumption)
    {
        throw UnsupportedSMTOpException("real number abstract single", contents);
    }
    PAIR RealNode::AbstractFloat(PAIR assumption)
    {
        if (IsVariable())
        {
            return assumption;
        }
        else if (IsConstant())
        {
            //Handle negative constants
            std::string str = contents.get_decimal_string(INT_MAX);
            if (str[0]=='(' && str[1]=='-')
            {
                str.erase(0,1);
                str.erase(1,1);
                str.erase(str.length()-1,1);
            }
            unsigned decimals = str.length();
            //If a decimal, get the precision and the size seperately
            if (str.find('.')>=0)
            {
                decimals--; //One less digit, since the . doesn't count
                str = str.substr(0,str.find('.'));
            }

            //Length in base 10 * 4 (log_2(10) + 1) to guarantee enough width
            return {APInt(str.length()*4, str, 10).abs()+1, decimals};
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
                    return PairMax(RealChild(1).AbstractFloat(assumption), RealChild(2).AbstractFloat(assumption));
                case Z3_OP_UMINUS:
                    //Only absolute value
                    return RealChild(0).AbstractFloat(assumption);
                case Z3_OP_SUB:
                case Z3_OP_ADD:
                    //Subtraction and addition can both grow (absolute value)
                    return PairPlus(RealChild(0).AbstractFloat(assumption),RealChild(1).AbstractFloat(assumption));
                case Z3_OP_MUL:
                    return PairMult(RealChild(0).AbstractFloat(assumption),RealChild(1).AbstractFloat(assumption));
                case Z3_OP_DIV:
                    //Can't add extra bits
                    return PairDiv(RealChild(0).AbstractFloat(assumption),RealChild(1).AbstractFloat(assumption));
                default:
                    throw UnsupportedSMTOpException("real operation", contents);
            }
        }
    }

    expr RealNode::ToSMTFloat(z3::sort type, std::map<std::string, expr> svariables)
    {
        if (IsVariable())
        {
            return svariables.at(contents.to_string());
        }
        else if (IsConstant())
        {
            //(*c).fpa_sort(5,11)

            //Handle negative constants
            std::string str = contents.get_decimal_string(INT_MAX);
            if (str[0]=='(' && str[1]=='-')
            {
                str.erase(0,1);
                str.erase(1,1);
                str.erase(str.length()-1,1);
            }

            return expr(scx,Z3_mk_fpa_to_fp_real(scx,scx.fpa_rounding_mode(),scx.real_val(str.c_str()),type));
        }
        else //Expression
        {
            expr val = scx.bool_val(true);
            switch (Op())
            {
                case Z3_OP_ITE:
                    return ite(BooleanChild(0).ToSMTFloat(type,svariables),RealChild(1).ToSMTFloat(type,svariables),RealChild(2).ToSMTFloat(type,svariables));
                case Z3_OP_UMINUS:
                    return -RealChild(0).ToSMTFloat(type,svariables);
                case Z3_OP_SUB:
                    return RealChild(0).ToSMTFloat(type,svariables) - RealChild(1).ToSMTFloat(type,svariables);
                case Z3_OP_ADD:
                    return RealChild(0).ToSMTFloat(type,svariables) + RealChild(1).ToSMTFloat(type,svariables);
                case Z3_OP_MUL:
                    return RealChild(0).ToSMTFloat(type,svariables) * RealChild(1).ToSMTFloat(type,svariables);
                case Z3_OP_DIV:
                    return RealChild(0).ToSMTFloat(type,svariables) / RealChild(1).ToSMTFloat(type,svariables);
                default:
                    throw UnsupportedSMTOpException("integer operation", contents);
            }
        }
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

    expr IntegerNode::ToSMT(unsigned width, std::map<std::string, expr> svariables, solver* sol)
    {
        if (IsVariable())
        {
            return svariables.at(contents.to_string());
        }
        else if (IsConstant())
        {
            //Handle negative constants
            std::string str = contents.to_string();
            bool isNegative = false;
            if (str[0] == '(' && str[1] == '-')
            {
                str.erase(0,1);
                str.erase(1,1);
                str.erase(str.length()-1,1);
                isNegative = true;
            }
            expr e = scx.bv_val(str.c_str(),width);
            if (isNegative)
            {
                if (noOverflow)
                {
                    sol->add(bvneg_no_overflow(e));
                }
                return -e;
            }
            else
            {
                return e;
            }
        }
        else //Expression
        {
            expr temp = scx.bool_val(true);
            expr val = scx.bool_val(true);
            switch (Op())
            {
                case Z3_OP_ITE:
                    return ite(BooleanChild(0).ToSMT(width,svariables,sol),IntegerChild(1).ToSMT(width,svariables,sol),IntegerChild(2).ToSMT(width,svariables,sol));
                case Z3_OP_UMINUS:
                    val = IntegerChild(0).ToSMT(width,svariables,sol);
                    if (noOverflow)
                    {
                        sol->add(bvneg_no_overflow(val));
                    }
                    return -val;
                case Z3_OP_INTERNAL: //integer absolute value
                    val = IntegerChild(0).ToSMT(width,svariables,sol);
                    return ite(val < 0, -val, val);
                case Z3_OP_SUB:
                    val = IntegerChild(0).ToSMT(width, svariables, sol);
                    for (int i = 1; i < contents.num_args(); i++)
                    {
                        temp = IntegerChild(i).ToSMT(width, svariables, sol);
                        if (noOverflow)
                        {
                            sol->add(bvsub_no_overflow(val,temp));
                            sol->add(bvsub_no_underflow(val,temp,true));
                        }
                        val = val - temp;
                    }
                    return val;
                    //left = IntegerChild(0).ToSMT(width,svariables,sol);
                    //right = IntegerChild(1).ToSMT(width,svariables,sol);
                    //sol->add(bvsub_no_overflow(left,right));
                    //sol->add(bvsub_no_underflow(left,right,true));
                    //return left - right;
                case Z3_OP_ADD:
                    val = IntegerChild(0).ToSMT(width, svariables, sol);
                    for (int i = 1; i < contents.num_args(); i++)
                    {
                        temp = IntegerChild(i).ToSMT(width, svariables, sol);
                        if (noOverflow)
                        {       
                            sol->add(bvadd_no_overflow(val,temp,true));
                            sol->add(bvadd_no_underflow(val,temp));
                        }
                        val = val + temp;
                    }
                    return val;
                    //left = IntegerChild(0).ToSMT(width,svariables,sol);
                    //right = IntegerChild(1).ToSMT(width,svariables,sol);
                    //sol->add(bvadd_no_overflow(left,right,true));
                    //sol->add(bvadd_no_underflow(left,right));
                    //return left + right;
                case Z3_OP_MUL:
                    val = IntegerChild(0).ToSMT(width, svariables, sol);
                    for (int i = 1; i < contents.num_args(); i++)
                    {
                        temp = IntegerChild(i).ToSMT(width, svariables, sol);
                        if (noOverflow)
                        {
                            sol->add(bvmul_no_overflow(val,temp,true));
                            sol->add(bvmul_no_underflow(val,temp));
                        }
                        val = val * temp;
                    }
                    return val;
                    //left = IntegerChild(0).ToSMT(width,svariables,sol);
                    //right = IntegerChild(1).ToSMT(width,svariables,sol);
                    //sol->add(bvmul_no_overflow(left,right,true));
                    //return left * right;
                case Z3_OP_IDIV:
                    val = IntegerChild(0).ToSMT(width, svariables, sol);
                    for (int i = 1; i < contents.num_args(); i++)
                    {
                        temp = IntegerChild(i).ToSMT(width, svariables, sol);
                        if (noOverflow)
                        {
                            sol->add(bvsdiv_no_overflow(val,temp));
                        }
                        val = val / temp;
                    }
                    return val;
                    //division operator overload is signed division
                    //left = IntegerChild(0).ToSMT(width,svariables,sol);
                    //right = IntegerChild(1).ToSMT(width,svariables,sol);
                    //sol->add(bvsdiv_no_overflow(left,right));
                    //return left / right;
                case Z3_OP_MOD:
                    return mod(IntegerChild(0).ToSMT(width,svariables,sol),IntegerChild(1).ToSMT(width,svariables,sol));
                default:
                    throw UnsupportedSMTOpException("integer operation", contents);
            }
        }
    }
*/