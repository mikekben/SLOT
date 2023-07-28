#include "LLVMNode.h"
#include "SLOTExceptions.h"


#ifndef SMTMAPPING
#define SMTMAPPING std::map<std::string, expr>
#endif

#ifndef LLVM_FUNCTION_NAME
#define LLVM_FUNCTION_NAME "SMT"
#endif


namespace SLOT
{
    LLVMNode::LLVMNode(bool t_shiftToMultiply, context& t_scx, const SMTMAPPING& t_variables, Value* t_contents) : shiftToMultiply(t_shiftToMultiply), scx(t_scx), variables(t_variables), contents(t_contents)
    {

    }
    

    std::unique_ptr<LLVMNode> LLVMNode::MakeLLVMNode(bool shiftToMultiply, context& scx, const SMTMAPPING& variables, Value *contents)
    {
        if (isa<Argument>(contents))
        {
            return std::make_unique<LLVMArgument>(shiftToMultiply, scx, variables, contents);
        }
        else if (isa<Constant>(contents))
        {
            return std::make_unique<LLVMConstant>(shiftToMultiply, scx, variables, contents);
        }
        else if (isa<Instruction>(contents))
        {
            Instruction* uv = ((Instruction*)contents);
            if (uv->getOpcode()==Instruction::Call)
            {
                return std::make_unique<LLVMIntrinsicCall>(shiftToMultiply, scx, variables, contents);
            }
            else if (uv->getOpcode()==Instruction::ICmp)
            {
                return std::make_unique<LLVMIcmp>(shiftToMultiply, scx, variables, contents);
            }
            else if (uv->getOpcode()==Instruction::FCmp)
            {
                return std::make_unique<LLVMFcmp>(shiftToMultiply, scx, variables, contents);
            }
            else
            {
                return std::make_unique<LLVMExpression>(shiftToMultiply, scx, variables, contents);
            }
        }
        else
        {
            throw UnsupportedLLVMOpException("node construction on non-instruction, argument, or constant", contents);
        }
    }

    z3::sort LLVMNode::SMTSort()
    {
        if (contents->getType()->isHalfTy())
        {
            return scx.fpa_sort(5,11);
        }
        else if (contents->getType()->isFloatTy())
        {
            return scx.fpa_sort(8,24);
        }
        else if (contents->getType()->isDoubleTy())
        {
            return scx.fpa_sort(11,53);
        }
        else if (contents->getType()->isFP128Ty())
        {
            return scx.fpa_sort(15,113);
        }
        else if (contents->getType()->isIntegerTy())
        {
            //1-bit integers are booleans
            if (contents->getType()->getIntegerBitWidth()==1)
            {
                return scx.bool_sort();
            }
            else
            {
                return scx.bv_sort(contents->getType()->getIntegerBitWidth());
            }
        }
        else
        {
            std::string type_str;
            llvm::raw_string_ostream rso(type_str);
            contents->print(rso);
            throw UnsupportedTypeException("unsupported LLVM type", rso.str());
        }
    }

    unsigned LLVMNode::Width()
    {
        if (SMTSort().is_bool())
        {
            return 1;
        }
        else if (SMTSort().is_bv())
        {
            return SMTSort().bv_size();
        }
        else //FPA case
        {
            return SMTSort().fpa_sbits() + SMTSort().fpa_ebits();
        }
    }


    //============================LLVMArgument==================================


    LLVMArgument::LLVMArgument(bool t_shiftToMultiply, context& t_scx, const SMTMAPPING& t_variables, Value* t_contents) : LLVMNode(t_shiftToMultiply, t_scx, t_variables, t_contents)
    {
        assert(isa<Argument>(contents));
    }

    expr LLVMArgument::ToSMT()
    {
        return variables.at(contents->getName().str());
    }


    //============================LLVMConstant==================================


    LLVMConstant::LLVMConstant(bool t_shiftToMultiply, context& t_scx, const SMTMAPPING& t_variables, Value* t_contents) : LLVMNode(t_shiftToMultiply, t_scx, t_variables, t_contents)
    {
        assert(isa<Constant>(contents));
    }

    expr LLVMConstant::ToSMT()
    {
        if (SMTSort().is_bool())
        {
            return scx.bool_val(((Constant*)contents)->isOneValue());
        }
        else if (SMTSort().is_bv())
        {
            return scx.bv_val(toString(((Constant*)contents)->getUniqueInteger(),10,false).c_str(), Width());
        }
        else //FPA case
        {
            char* s;
            ((ConstantFP*)contents)->getValue().convertToHexString(s, 0, true, RoundingMode::NearestTiesToEven);
            return scx.bv_val(s, Width()).mk_from_ieee_bv(SMTSort());
        }
    }

    //============================LLVMIntrinsicCall==================================
    LLVMIntrinsicCall::LLVMIntrinsicCall(bool t_shiftToMultiply, context& t_scx, const SMTMAPPING& t_variables, Value* t_contents) : LLVMExpression(t_shiftToMultiply, t_scx, t_variables, t_contents)
    {
        assert(Opcode() == Instruction::Call);
    }

    expr LLVMIntrinsicCall::FPClassCheck(context& scx, expr val, int64_t bits)
    {
        switch(bits)
        {
            case 3:
                return val.mk_is_nan();
            case 516:
                return val.mk_is_inf();
            case 96:
                return val.mk_is_zero();
            case 264:
                return val.mk_is_normal();
            case 144:
                return val.mk_is_subnormal();
            case 60:
                return expr(scx,Z3_mk_fpa_is_negative(scx, val));
            case 960:
                return expr(scx,Z3_mk_fpa_is_positive(scx, val));
            default:
                throw UnsupportedSMTOpException("unsupported floating point class check flag bitmask", val);
        }
    }

    expr LLVMIntrinsicCall::ToSMT()
    {
        Intrinsic::ID id = ((CallInst*)contents)->getCalledFunction()->getIntrinsicID();
        //Intrinsics which are resonable in the integer context
        expr arg(scx);
        expr left(scx);
        expr right(scx);
        expr temp(scx);
        expr_vector v(scx);
        if (id == Function::lookupIntrinsicID("llvm.is.fpclass"))
        {
            //Can't be handled in the switch
            int64_t bits = ((ConstantInt*)(AsInstruction()->getOperand(1)))->getSExtValue();
            return LLVMIntrinsicCall::FPClassCheck(scx, Child(0)->ToSMT(), bits);
        }
        switch (id)
        {
            case Intrinsic::abs:
                arg = Child(0)->ToSMT();
                return ite(arg < Zero(), -arg, arg);
            case Intrinsic::smin:
                left = Child(0)->ToSMT();
                right = Child(1)->ToSMT();
                return ite(left <= right,left,right);
            case Intrinsic::smax:
                left = Child(0)->ToSMT();
                right = Child(1)->ToSMT();
                return ite(left <= right,right,left);
            case Intrinsic::fabs:
                return z3::abs(Child(0)->ToSMT());
            case Intrinsic::fma:
                return z3::fma(Child(0)->ToSMT(),Child(1)->ToSMT(),Child(2)->ToSMT(), scx.fpa_rounding_mode());
            case Intrinsic::sqrt:
                return z3::sqrt(Child(0)->ToSMT(), scx.fpa_rounding_mode());
            case Intrinsic::minnum:
                return min(Child(0)->ToSMT(),Child(1)->ToSMT());
            case Intrinsic::maxnum:
                return max(Child(0)->ToSMT(),Child(1)->ToSMT());
            case Intrinsic::bswap:
                //Reverse the order of bytes
                arg = Child(0)->ToSMT();
                v = expr_vector(scx);
                for (int i = (Width()/8)-1; i>=0; i--)
                {
                    v.push_back(arg.extract(Width()-(8*i)-1, Width()-(8*(i+1))));
                }
                return concat(v);
            case Intrinsic::ctpop:
                //Count the number of 1 bits
                arg = Child(0)->ToSMT();
                temp = arg.extract(0,0);
                for (int i = 1; i<Width(); i++)
                {
                    temp = temp + arg.extract(i,i);
                }
                return temp;
            case Intrinsic::bitreverse:
                //Reverse the order of bits
                arg = Child(0)->ToSMT();
                v = expr_vector(scx);
                for (int i = Width()-1; i>=0; i++)
                {
                    v.push_back(arg.extract(i,i));
                }
                return concat(v);
            case Intrinsic::fshl:
                //Funnel shift
                return shl(concat(Child(0)->ToSMT(), Child(1)->ToSMT()), Child(2)->ToSMT()).extract((Width()*2)-1, Width());
            case Intrinsic::fshr:
                //Funnel shift
                return lshr(concat(Child(0)->ToSMT(),Child(1)->ToSMT()),Child(2)->ToSMT()).extract(Width()-1,0);
            case Intrinsic::usub_sat:
                //Subtraction without underflow (clamped to 0)
                left = Child(0)->ToSMT();
                right = Child(1)->ToSMT();
                return ite(ule(left, right), Zero(), left - right);
            case Intrinsic::uadd_sat:
                //Addition without overflow (clamped to max, i.e. -1)
                left = Child(0)->ToSMT();
                right = Child(1)->ToSMT();
                return ite(ule(left + right, left), scx.bv_val(-1, Width()), left + right);
            case Intrinsic::umin:
                left = Child(0)->ToSMT();
                right = Child(1)->ToSMT();
                return ite(ule(left, right), left, right);
            case Intrinsic::umax:
                left = Child(0)->ToSMT();
                right = Child(1)->ToSMT();
                return ite(ule(left,right),right,left);
            default:
                throw UnsupportedLLVMOpException("unsupported intrinsic function", contents);
        }
    }


    //============================LLVMIcmp==================================
    LLVMIcmp::LLVMIcmp(bool t_shiftToMultiply, context& t_scx, const SMTMAPPING& t_variables, Value* t_contents) : LLVMExpression(t_shiftToMultiply, t_scx, t_variables, t_contents)
    {
        assert(Opcode() == Instruction::ICmp);
    }

    expr LLVMIcmp::ToSMT()
    {
        ICmpInst* vi = ((ICmpInst*)contents);
        
        //Operator overloads for EQ and NE work for both booleans and integers
        if (Predicate()==CmpInst::ICMP_EQ)
        {
            //This arose from a floating point = comparison. Important since there is no floating point to bitvector bitcast in SMT
            if (isa<BitCastInst>(vi->getOperand(0)) && isa<BitCastInst>(vi->getOperand(1)))
            {

                //unique_ptr<LLVMExpression>{static_cast<LLVMExpression*>(old.release())}

                return std::unique_ptr<LLVMExpression>{static_cast<LLVMExpression*>(Child(0).release())}->Child(0)->ToSMT() == std::unique_ptr<LLVMExpression>{static_cast<LLVMExpression*>(Child(1).release())}->Child(0)->ToSMT();
            }
            else if (isa<BitCastInst>(vi->getOperand(0)))
            {
                expr left = std::unique_ptr<LLVMExpression>{static_cast<LLVMExpression*>(Child(0).release())}->Child(0)->ToSMT();
                expr right = Child(1)->ToSMT().mk_from_ieee_bv(left.get_sort());
                return left == right;
            }
            else if (isa<BitCastInst>(vi->getOperand(1)))
            {
                //Reverse order so we can do right.get_sort()
                expr right = std::unique_ptr<LLVMExpression>{static_cast<LLVMExpression*>(Child(1).release())}->Child(0)->ToSMT();
                expr left = Child(0)->ToSMT().mk_from_ieee_bv(right.get_sort());
                return left == right;
            }
            else
            { 
                //Regular case
                return Child(0)->ToSMT() == Child(1)->ToSMT();
            }
        }
        else if (vi->getPredicate()==CmpInst::ICMP_NE)
        {
            //This arose from a floating point distinct comparison. Important since there is no floating point to bitvector bitcast in SMT
            if (isa<BitCastInst>(vi->getOperand(0)) && isa<BitCastInst>(vi->getOperand(1)))
            {
                return std::unique_ptr<LLVMExpression>{static_cast<LLVMExpression*>(Child(0).release())}->Child(0)->ToSMT() != std::unique_ptr<LLVMExpression>{static_cast<LLVMExpression*>(Child(1).release())}->Child(0)->ToSMT();
            }
            else if (isa<BitCastInst>(vi->getOperand(0)))
            {
                expr left = std::unique_ptr<LLVMExpression>{static_cast<LLVMExpression*>(Child(0).release())}->Child(0)->ToSMT();
                expr right = Child(1)->ToSMT().mk_from_ieee_bv(left.get_sort());
                return left != right;
            }
            else if (isa<BitCastInst>(vi->getOperand(1)))
            {
                //Reverse order so we can do right.get_sort()
                expr right = std::unique_ptr<LLVMExpression>{static_cast<LLVMExpression*>(Child(1).release())}->Child(0)->ToSMT();
                expr left = Child(0)->ToSMT().mk_from_ieee_bv(right.get_sort());
                return left != right;
            }
            else
            {
                //Regular case
                return Child(0)->ToSMT() != Child(1)->ToSMT();
            }
        }
        else
        {
            //Can evaluate the children regularly
            expr left = Child(0)->ToSMT();
            expr right = Child(1)->ToSMT();
            switch(Predicate())
            {
                case CmpInst::ICMP_SGT:
                    return left > right;
                case CmpInst::ICMP_SGE:
                    return left >= right;
                case CmpInst::ICMP_SLT:
                    return left < right;
                case CmpInst::ICMP_SLE:
                    return left <= right;
                case CmpInst::ICMP_UGT:
                    return ugt(left,right);
                case CmpInst::ICMP_UGE:
                    return uge(left,right);
                case CmpInst::ICMP_ULT:
                    return ult(left,right);
                case CmpInst::ICMP_ULE:
                    return ule(left,right);
                default:
                    throw UnsupportedLLVMOpException("unsupported ICMP predicate", contents);
            }
        }
    }



    //============================LLVMFcmp==================================
    LLVMFcmp::LLVMFcmp(bool t_shiftToMultiply, context& t_scx, const SMTMAPPING& t_variables, Value* t_contents) : LLVMExpression(t_shiftToMultiply, t_scx, t_variables, t_contents)
    {
        assert(Opcode() == Instruction::FCmp);
    }

    expr LLVMFcmp::ToSMT()
    {
        expr left = Child(0)->ToSMT();
        expr right = Child(1)->ToSMT();
        switch (Predicate())
        {
            case CmpInst::FCMP_FALSE:
                return scx.bool_val(false);
            //Ordered (not both NaN, matches SMT semantics)
            case CmpInst::FCMP_OEQ:
                return fp_eq(left, right);
            case CmpInst::FCMP_OGT:
                return left > right;
            case CmpInst::FCMP_OGE:
                return left >= right;
            case CmpInst::FCMP_OLT:
                return left < right;
            case CmpInst::FCMP_OLE:
                return left <= right;
            case CmpInst::FCMP_ONE:
                return (!left.mk_is_nan()) && (!right.mk_is_nan()) && (!fp_eq(left,right));
            case CmpInst::FCMP_ORD:
                return (!left.mk_is_nan()) && (!right.mk_is_nan());
            //Unordered (either is NaN or the comparison)
            case CmpInst::FCMP_UEQ:
                return left.mk_is_nan() || right.mk_is_nan() || fp_eq(left,right);
            case CmpInst::FCMP_UGT:
                return left.mk_is_nan() || right.mk_is_nan() || (left > right);
            case CmpInst::FCMP_UGE:
                return left.mk_is_nan() || right.mk_is_nan() || (left >= right);
            case CmpInst::FCMP_ULT:
                return left.mk_is_nan() || right.mk_is_nan() || (left < right);
            case CmpInst::FCMP_ULE:
                return left.mk_is_nan() || right.mk_is_nan() || (left <= right);
            case CmpInst::FCMP_UNE:
                return left.mk_is_nan() || right.mk_is_nan() || (!fp_eq(left, right));
            case CmpInst::FCMP_UNO:
                return left.mk_is_nan() || right.mk_is_nan();
            case CmpInst::FCMP_TRUE:
                return scx.bool_val(true);
            default:
                throw UnsupportedLLVMOpException("unsupported FCMP predicate", contents);
        }
    }



    //============================LLVMExpression==================================

    LLVMExpression::LLVMExpression(bool t_shiftToMultiply, context& t_scx, const SMTMAPPING& t_variables, Value* t_contents) : LLVMNode(t_shiftToMultiply, t_scx, t_variables, t_contents)
    {
        assert(isa<Instruction>(contents));
    }

    expr LLVMExpression::ToSMT()
    {
        //uv = AsInstruction()
        Value* child;
        expr arg(scx);
        expr left(scx);
        expr right(scx);
        int rr;
        switch (Opcode()) // Instructions
        {
            //Special case: umul.with.overflow followed by extract value
            case Instruction::ExtractValue:
                child = ((Instruction*)contents)->getOperand(0);
                if (isa<CallInst>(child) && ((CallInst*)child)->getCalledFunction()->getIntrinsicID()==Intrinsic::umul_with_overflow)
                {
                    expr left = Child(0)->ToSMT();
                    expr right = Child(1)->ToSMT();
                    expr zero = scx.bv_val(0,left.get_sort().bv_size()); //Not the same as Zero()
                    return ite(((left == zero) || (right == zero)),scx.bool_val(false),!(((left*right)/left)==right));
                }
                else
                {
                    throw UnsupportedLLVMOpException("extract value without umul.with.overflow", contents);
                }
            case Instruction::FNeg:
                //Z3 api redefines operators
                return -Child(0)->ToSMT();
            case Instruction::FPToUI:
                return fpa_to_ubv(Child(0)->ToSMT(), Width());
            case Instruction::FPToSI:
                return fpa_to_sbv(Child(0)->ToSMT(), Width());
            case Instruction::FPExt:
            case Instruction::FPTrunc:
                return fpa_to_fpa(Child(0)->ToSMT(), SMTSort());
            case Instruction::SIToFP:
                return sbv_to_fpa(Child(0)->ToSMT(), SMTSort());
            case Instruction::UIToFP:
                return ubv_to_fpa(Child(0)->ToSMT(), SMTSort());
            //Unary bitvector instructions
            case Instruction::BitCast:
                //Bitcast from bitvector to floating point
                if(SMTSort().is_fpa())
                {
                    return Child(0)->ToSMT().mk_from_ieee_bv(SMTSort());
                }
                else
                {
                    //There is no floating to bitvector bitcast equivalent in SMT since NaN has multiple representations
                    //Handled in the icmp conversion
                    throw UnsupportedLLVMOpException("fp to bitvector bitcast", contents);
                }
            case Instruction::Trunc:
                return Child(0)->ToSMT().extract(Width()-1, 0);
            case Instruction::ZExt:
                arg = Child(0)->ToSMT();
                if (arg.is_bool()) //optimizer created zext i1
                {
                    return zext(ite(arg, scx.bv_val(1,1), scx.bv_val(0,1)), Width()-1);
                }
                else
                {
                    return zext(arg, Width()-std::unique_ptr<LLVMExpression>{static_cast<LLVMExpression*>(Child(0).release())}->Width());
                }
            case Instruction::SExt:
                arg = Child(0)->ToSMT();
                if (arg.is_bool()) //optimizer created sext i1
                {
                    //The optimizer may introduce sext i1 ...
                    return sext(ite(arg, scx.bv_val(1,1), scx.bv_val(0,1)), Width()-1);
                }
                else
                {
                    return sext(arg, Width()-std::unique_ptr<LLVMExpression>{static_cast<LLVMExpression*>(Child(0).release())}->Width());
                }      
            case Instruction::Freeze:
                //Frontend guarantees no undefined behavior, so freeze always returns its argument
                return Child(0)->ToSMT();
            //Binary instructions (boolean or bitvector)
            case Instruction::And:
                left = Child(0)->ToSMT();
                right = Child(1)->ToSMT();
                return left.is_bool() ? (left && right) : (left & right);
            case Instruction::Or:
                left = Child(0)->ToSMT();
                right = Child(1)->ToSMT();
                return left.is_bool() ? (left || right) : (left | right);
            case Instruction::Xor:
                //The type check is built into the z3 ^ operator overload
                return Child(0)->ToSMT() ^ Child(1)->ToSMT();
            //Binary bitvector instructions
            case Instruction::Shl:
                left = Child(0)->ToSMT();
                right = Child(1)->ToSMT();
                // Check for shift left by a constant; this can be replaced with multiplication
                if (shiftToMultiply && right.is_const() && ((rr = std::atoi(right.to_string().c_str())) > 0))
                {
                    int i = 1;
                    while (rr > 0) { i*=2; rr--;}
                    return left * scx.bv_val(i,Width());
                }
                else
                {
                    return shl(left,right);
                }
            case Instruction::LShr:
                return lshr(Child(0)->ToSMT(),Child(1)->ToSMT());
            case Instruction::AShr:
                return ashr(Child(0)->ToSMT(),Child(1)->ToSMT());
            case Instruction::UDiv:
                return udiv(Child(0)->ToSMT(),Child(1)->ToSMT());
            case Instruction::URem:
                return urem(Child(0)->ToSMT(),Child(1)->ToSMT());
            case Instruction::SRem:
                return srem(Child(0)->ToSMT(),Child(1)->ToSMT());
            //Bitvector and floating instructions (double operator overload meaning)
            case Instruction::Add:
            case Instruction::FAdd:
                return Child(0)->ToSMT() + Child(1)->ToSMT();
            case Instruction::Sub:
            case Instruction::FSub:
                return Child(0)->ToSMT() - Child(1)->ToSMT();
            case Instruction::Mul:
            case Instruction::FMul:
                return Child(0)->ToSMT() * Child(1)->ToSMT();
            case Instruction::SDiv:
            case Instruction::FDiv:
                return Child(0)->ToSMT() / Child(1)->ToSMT();
            //Binary floating instructions
            case Instruction::FRem:
                return rem(Child(0)->ToSMT(), Child(1)->ToSMT());
            //Select instruction
            case Instruction::Select:
                return ite(Child(0)->ToSMT(),Child(1)->ToSMT(),Child(2)->ToSMT());
            default:
                throw UnsupportedLLVMOpException("unsupported LLVM instruction", contents);

        }
    }
}