#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/Analysis/LazyValueInfo.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/AggressiveInstCombine/AggressiveInstCombine.h"
#include "llvm/Transforms/Scalar/Reassociate.h"
#include "llvm/Transforms/Scalar/SCCP.h"
#include "llvm/Transforms/Scalar/DCE.h"
#include "llvm/Transforms/Scalar/ADCE.h"
#include "llvm/Transforms/Scalar/InstSimplifyPass.h"
#include "llvm/Transforms/Scalar/GVN.h"

#include"z3++.h"
#include"smmintrin.h"
#include <algorithm>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <vector>
#include <exception>
#include <fstream>
#include <streambuf>
#include <iostream>
#include <string>
#include <regex>
#include <unistd.h>
#include <memory>
//#include <iostream>

using namespace llvm;
using namespace z3;
//using namespace std;




static std::unique_ptr<LLVMContext> TheContext;
static std::unique_ptr<Module> TheModule;
static std::unique_ptr<IRBuilder<>> Builder;
static bool isInteger;
static bool shiftToMultiply;
static int integerWidth;

class SMTTypeBuilderException : public std::exception {
   
  z3::sort expected;
  expr actual;
  std::string string;

  public:
    SMTTypeBuilderException(z3::sort t_expected, expr t_actual) : expected(t_expected), actual(t_actual) 
    {
      string = "Attempted to build expression \"" + actual.to_string() + "\" with type " + actual.get_sort().name().str() + " as having type " + expected.name().str() + ".";
    }
    const char * what () const throw () 
    {
      return string.c_str();
    }
};

class SMTUnsupportedOperationException : public std::exception {
  expr actual;
  std::string type;
  std::string string;

  public:
    SMTUnsupportedOperationException(std::string t_type, expr t_actual) : type(t_type), actual(t_actual)
    {
      string = "Unsupported operation in expression \"" + actual.to_string() + "\" while building a " + type + ".";
    }
    const char * what () const throw () 
    {
      return string.c_str();
    }
};

class SMTUnsupportedTypeException : public std::exception {
  std::string found;
  std::string string;

  public:
    SMTUnsupportedTypeException(std::string t_found) : found(t_found)
    {
      string = "Encountered SMT variable with unsupported type: " + found + ".";
    }
    const char * what () const throw () 
    {
      return string.c_str();
    }
};

class LLVMUnsupportedException : public std::exception {
  std::string found;
  std::string description;
  std::string string;

  public:
    LLVMUnsupportedException(std::string t_description, std::string t_found) : description(t_description), found(t_found)
    {
      string = "Encountered unsupported LLVM expression (" + description + "): " + found + ".";
    }
    const char * what () const throw () 
    {
      return string.c_str();
    }
};

class NotIntegerException : public std::exception {
  std::string found;
  std::string string;

  public:
    NotIntegerException(std::string t_found) : found(t_found)
    {
      string = "Encountered expression " + found + " in an integer-only context.";
    }
    const char * what () const throw () 
    {
      return string.c_str();
    }
};

//===----------------------------------------------------------------------===//
// General SMT Node Classes
//===----------------------------------------------------------------------===//

class SMT
{
  public:
    context ctx;
    expr contents;
    std::map<std::string, Value *> variables;
    SMT(std::map<std::string, Value*> t_variables, expr t_contents) : contents(t_contents), variables(t_variables) { }
    virtual Value * codegen() = 0;
};

class IntegerSMT : public SMT
{
  public:
    static bool IsComparison(expr expression);
    static IntegerSMT* MakeIntegerSMT(std::map<std::string, Value *> variables, expr expression);
    IntegerSMT(std::map<std::string, Value*> t_variables, expr t_contents) : SMT(t_variables, t_contents) {}

};
class ConstIntegerSMT : public IntegerSMT 
{
  std::string value;

  public:
    ConstIntegerSMT(std::map<std::string, Value *> t_variables, expr t_contents);
    Value * codegen() override;
};
class VariableIntegerSMT : public IntegerSMT 
{
  std::string name;
  
  public:
    VariableIntegerSMT(std::map<std::string, Value *> t_variables, expr t_contents);
    Value * codegen() override;
};
class ExprIntegerSMT : public IntegerSMT {
  Z3_decl_kind op;
  std::vector<SMT*> children;
  
  public:
    ExprIntegerSMT(std::map<std::string, Value *> t_variables, expr t_contents);
    Value * codegen() override;
};



class FloatingSMT : public SMT
{
  public:
    unsigned int width;
    unsigned int sbits;
    static bool IsClassCheck(expr expression);
    static bool IsClassCheck(Z3_decl_kind k);
    static bool IsComparison(expr expression);
    static Type * ToFloating(int width);
    static void CheckRM(expr e);
    static bool IsRoundingMode(expr e);
    static Value * LlClass(Value * value, Z3_decl_kind op);
    static Value * LlFNE(int width, Value * left, Value * right);
    static FloatingSMT* MakeFloatingSMT(std::map<std::string, Value *> variables, expr expression);
    FloatingSMT(std::map<std::string, Value*> t_variables, expr t_contents) : SMT(t_variables, t_contents) {}

};
class VariableFloatingSMT : public FloatingSMT 
{
  std::string name;
  
  public:
    VariableFloatingSMT(std::map<std::string, Value *> t_variables, expr t_contents);
    Value * codegen() override;
};
enum ToFPType {bitcast, tsigned, fpfp};
class ExprFloatingSMT : public FloatingSMT {
  Z3_decl_kind op;
  std::vector<SMT*> children;
  std::vector<int> params;
  ToFPType tft;
  
  public:
    ExprFloatingSMT(std::map<std::string, Value *> t_variables, expr t_contents);
    Value * codegen() override;
};



class BitvectorSMT : public SMT
{
  public:
    unsigned int width;
    static bool IsSignedComparison(expr expression);
    static bool IsUnsignedComparison(expr expression);
    static bool IsComparison(expr expression);
    static Value * LlIsZero(Value * val);
    static Value * LlIsNegative(Value * val);
    static Value * LlIsPositive(Value * val);
    static Value * LlURem(Value * left, Value * right);
    static BitvectorSMT* MakeBitvectorSMT(std::map<std::string, Value *> variables, expr expression);
    BitvectorSMT(std::map<std::string, Value*> t_variables, expr t_contents) : SMT(t_variables, t_contents) {}

};
class ConstBitvectorSMT : public BitvectorSMT 
{
  std::string value;
  bool isBinary;

  public:
    ConstBitvectorSMT(std::map<std::string, Value *> t_variables, expr t_contents);
    Value * codegen() override;
};
class VariableBitvectorSMT : public BitvectorSMT 
{
  std::string name;
  
  public:
    VariableBitvectorSMT(std::map<std::string, Value *> t_variables, expr t_contents);
    Value * codegen() override;
};
class ExprBitvectorSMT : public BitvectorSMT {
  Z3_decl_kind op;
  std::vector<SMT*> children;
  std::vector<int> params;
  
  public:
    ExprBitvectorSMT(std::map<std::string, Value *> t_variables, expr t_contents);
    Value * codegen() override;
};


enum Category {boolean, bitvector, floating, integer};
class BooleanSMT : public SMT 
{
  public:
    static BooleanSMT* MakeBooleanSMT(std::map<std::string, Value *> variables, expr expression);
    BooleanSMT(std::map<std::string, Value*> t_variables, expr t_contents) : SMT(t_variables, t_contents) {}
};
class ConstBooleanSMT : public BooleanSMT 
{
  bool value;

  public:
    ConstBooleanSMT(std::map<std::string, Value *> t_variables, expr t_contents);
    Value * codegen() override;
};
class ExprBooleanSMT : public BooleanSMT {
  Z3_decl_kind op;
  std::vector<SMT*> children;
  Category childCategory;
  
  public:
    ExprBooleanSMT(std::map<std::string, Value *> t_variables, expr t_contents);
    Value * codegen() override;
};



class ConstraintSMT  
{
  expr_vector contents;
  std::vector<BooleanSMT*> assertions;
  std::map<std::string, Value *> variables;
  Function* fun;
  std::string string;

  public:
    ConstraintSMT(std::string t_string);
    Value *codegen();
};


//===----------------------------------------------------------------------===//
// Integers
//===----------------------------------------------------------------------===//

bool IntegerSMT::IsComparison(expr expression)
{
  Z3_decl_kind k = expression.decl().decl_kind();
  bool direct = (k == Z3_OP_LT || k == Z3_OP_LE || k == Z3_OP_GT || k == Z3_OP_GE);
  return expression.num_args() >= 1 && ((expression.arg(0).is_int() && (expression.is_eq() || expression.is_distinct())) || direct);
}


ConstIntegerSMT::ConstIntegerSMT(std::map<std::string, Value *> t_variables, expr t_contents) : IntegerSMT(t_variables, t_contents)
{
  value = contents.to_string();
}
Value * ConstIntegerSMT::codegen()
{
  return ConstantInt::get(IntegerType::get(*TheContext, integerWidth), value, 10);
}


VariableIntegerSMT::VariableIntegerSMT(std::map<std::string, Value *> t_variables, expr t_contents) : IntegerSMT(t_variables, t_contents)
{
  name = contents.to_string();
}
Value * VariableIntegerSMT::codegen()
{
    return variables[name];
}

ExprIntegerSMT::ExprIntegerSMT(std::map<std::string, Value *> t_variables, expr t_contents) : IntegerSMT(t_variables, t_contents)
{
  op = contents.decl().decl_kind();

  //special instructions with non-integer arguments
  if (op == Z3_OP_ITE)
  {
    children.push_back(BooleanSMT::MakeBooleanSMT(variables, contents.arg(0)));
    children.push_back(IntegerSMT::MakeIntegerSMT(variables, contents.arg(1)));
    children.push_back(IntegerSMT::MakeIntegerSMT(variables, contents.arg(2)));
  }
  else
  {
    unsigned argCnt = contents.num_args();
    for (unsigned i = 0; i < argCnt; i++)
    {
      children.push_back(IntegerSMT::MakeIntegerSMT(variables,contents.arg(i)));
    }
  }
}

Value * ExprIntegerSMT::codegen()
{
  if (op == Z3_OP_ITE)
  {
    assert(children.size()==3);
    return Builder->CreateSelect(children[0]->codegen(),children[1]->codegen(), children[2]->codegen());
  }
  else if (op == Z3_OP_UMINUS)
  {
    return Builder->CreateSub(ConstantInt::get(IntegerType::get(*TheContext, integerWidth), 0),children[0]->codegen());
  }
  else if (op == Z3_OP_SUB)
  {
    return Builder->CreateSub(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_ADD)
  {
    return Builder->CreateAdd(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_MUL)
  {
    return Builder->CreateMul(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_DIV)
  {
    return Builder->CreateSDiv(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_MOD)
  {
    return Builder->CreateSRem(children[0]->codegen(),children[1]->codegen());
  }
  //Z3 internally renames integer abs from SMTLIB
  else
  {
    throw std::out_of_range("Unsupported integer expression");
  }
}

IntegerSMT* IntegerSMT::MakeIntegerSMT(std::map<std::string, Value *> variables, expr expression)
{
  if (!expression.is_int())
  {
    context c;
    throw SMTTypeBuilderException(expression.get_sort(),expression);
  }
  else if (expression.is_const() && variables[expression.to_string()]) //Variable case
  {
    return new VariableIntegerSMT(variables, expression);
  }
  else if (expression.is_const()) //Constant case
  {
    return new ConstIntegerSMT(variables, expression);
  }
  else //Expression case
  {
    return new ExprIntegerSMT(variables, expression);
  }
}



//===----------------------------------------------------------------------===//
// Floating point
//===----------------------------------------------------------------------===//

bool FloatingSMT::IsClassCheck(expr expression)
{
  return FloatingSMT::IsClassCheck(expression.decl().decl_kind());
}
bool FloatingSMT::IsClassCheck(Z3_decl_kind k)
{
  return (k == Z3_OP_FPA_IS_NAN || k == Z3_OP_FPA_IS_INF || k == Z3_OP_FPA_IS_ZERO || k == Z3_OP_FPA_IS_NORMAL || k == Z3_OP_FPA_IS_SUBNORMAL || k == Z3_OP_FPA_IS_NEGATIVE || k == Z3_OP_FPA_IS_POSITIVE);
}
bool FloatingSMT::IsComparison(expr expression)
{
  Z3_decl_kind k = expression.decl().decl_kind();
  bool direct = (k == Z3_OP_FPA_EQ || k == Z3_OP_FPA_LT || k == Z3_OP_FPA_GT || k == Z3_OP_FPA_LE || k == Z3_OP_FPA_GE);
  return expression.num_args() >= 1 && ((expression.arg(0).is_fpa() && (expression.is_eq() || expression.is_distinct())) || direct);
}
Type * FloatingSMT::ToFloating(int width)
{
  if (width == 16)
  {
    return Type::getHalfTy(*TheContext);
  }
  else if (width == 32)
  {
    return Type::getFloatTy(*TheContext);
  }
  else if (width == 64)
  {
    return Type::getDoubleTy(*TheContext);
  }
  else if (width == 128)
  {
    return Type::getFP128Ty(*TheContext);
  }
  else
  {
    throw std::out_of_range("Unsupported floating point type (only 16, 32, 64, and 128 supported).");
  }
}

void FloatingSMT::CheckRM(expr e)
{
  if (e.decl().decl_kind() != Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN) //Round to nearest, ties to even; only one supported in LLVM
  {
    throw std::out_of_range("Unsupported floating point rounding mode (only RNE supported).");
  }
}
bool FloatingSMT::IsRoundingMode(expr e)
{
  Z3_decl_kind k = e.decl().decl_kind();
  return k == Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN || 
         k == Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY ||
         k == Z3_OP_FPA_RM_TOWARD_POSITIVE ||
         k == Z3_OP_FPA_RM_TOWARD_NEGATIVE ||
         k == Z3_OP_FPA_RM_TOWARD_ZERO;
}

//TODO: Function now empty
Value * FloatingSMT::LlClass(Value * value, Z3_decl_kind op)
{
  return Builder->CreateAnd(value,value);
}

Value * FloatingSMT::LlFNE(int width, Value * left, Value * right)
{
  IntegerType * iType = IntegerType::get(*TheContext,width);
  Value* lb = Builder->CreateBitCast(left,iType);
  Value* rb = Builder->CreateBitCast(right,iType);

  //Not both NAN or different bits
  return Builder->CreateOr(Builder->CreateNot(Builder->CreateAnd(FloatingSMT::LlClass(lb, Z3_OP_FPA_IS_NAN), FloatingSMT::LlClass(rb, Z3_OP_FPA_IS_NAN))), Builder->CreateICmpNE(lb, rb));
}

VariableFloatingSMT::VariableFloatingSMT(std::map<std::string, Value *> t_variables, expr t_contents) : FloatingSMT(t_variables, t_contents)
{

  name = contents.to_string();
  sbits = contents.get_sort().fpa_sbits();
  width = sbits + contents.get_sort().fpa_ebits();
  FloatingSMT::ToFloating(width);
  //ToFloating checks for the right total width, but we shouldn't have eb+sb = 64 but not 11 and 53
  if (!(sbits == 11 || sbits == 24 || sbits == 53 || sbits == 113))
  {
    throw std::out_of_range("Unsupported floating point type (only 16, 32, 64, and 128 supported).");
  }
  
}
Value * VariableFloatingSMT::codegen()
{
    return variables[name];
}

ExprFloatingSMT::ExprFloatingSMT(std::map<std::string, Value *> t_variables, expr t_contents) : FloatingSMT(t_variables, t_contents)
{
  op = contents.decl().decl_kind();
  //std::cout<< "making floating point expression: " << contents.to_string() << "\n";

  sbits = contents.get_sort().fpa_sbits();
  width = sbits + contents.get_sort().fpa_ebits();
  FloatingSMT::ToFloating(width);
  //ToFloating checks for the right total width, but we shouldn't have eb+sb = 64 but not 11 and 53
  assert(sbits == 11 || sbits == 24 || sbits == 53 || sbits == 113);

  //special instructions with non-FP arguments
  if (op == Z3_OP_ITE)
  {
    children.push_back(BooleanSMT::MakeBooleanSMT(variables, contents.arg(0)));
    children.push_back(FloatingSMT::MakeFloatingSMT(variables, contents.arg(1)));
    children.push_back(FloatingSMT::MakeFloatingSMT(variables, contents.arg(2)));
  }
  //Single Z3 op representing different functions
  else if (op == Z3_OP_FPA_TO_FP)
  {
    if (contents.num_args()==1)
    {
      //Bitcast conversion bitvector to floating
      children.push_back(BitvectorSMT::MakeBitvectorSMT(variables, contents.arg(0)));
      tft = bitcast;
    }
    else if (contents.arg(1).is_bv())
    {
      //Signed numeric conversion bitvector to floating
      FloatingSMT::CheckRM(contents.arg(0));
      children.push_back(BitvectorSMT::MakeBitvectorSMT(variables, contents.arg(1)));
      tft = tsigned;
    }
    else if (contents.arg(1).is_fpa())
    {
      //Conversion from floating to floating
      FloatingSMT::CheckRM(contents.arg(0));
      children.push_back(FloatingSMT::MakeFloatingSMT(variables, contents.arg(1)));
      tft = fpfp;
    }
    else
    {
      SMTUnsupportedOperationException("to_fp on unsupported argument type", contents);
    }
  }
  else if (op == Z3_OP_FPA_TO_FP_UNSIGNED)
  {
      //Unsigned numeric conversion bitvector to floating
      FloatingSMT::CheckRM(contents.arg(0));
      children.push_back(BitvectorSMT::MakeBitvectorSMT(variables, contents.arg(1)));
  }
  //Construct a floating point from sign, exponent, significand
  else if (op == Z3_OP_FPA_FP)
  {
    children.push_back(BitvectorSMT::MakeBitvectorSMT(variables, contents.arg(0)));
    children.push_back(BitvectorSMT::MakeBitvectorSMT(variables, contents.arg(1)));
    children.push_back(BitvectorSMT::MakeBitvectorSMT(variables, contents.arg(2)));
  }
  else
  {
    unsigned argCnt = contents.num_args();
    unsigned i = 0;
    if (argCnt > 0 && FloatingSMT::IsRoundingMode(contents.arg(0)))
    {
      FloatingSMT::CheckRM(contents.arg(0));
      i++;
    }
    for (; i < argCnt; i++)
    {
        children.push_back(FloatingSMT::MakeFloatingSMT(variables,contents.arg(i)));
    }
  }
}

Value * ExprFloatingSMT::codegen()
{
  if (op == Z3_OP_ITE)
  {
    assert(children.size()==3);
    return Builder->CreateSelect(children[0]->codegen(),children[1]->codegen(), children[2]->codegen());
  }
  else if (op == Z3_OP_FPA_TO_FP_UNSIGNED)
  {
    assert(children.size()==1);
    return Builder->CreateUIToFP(children[0]->codegen(), FloatingSMT::ToFloating(width));
    //return builder.uitofp(res,bits_to_floating(node.decl().params()))
  }
  else if (op == Z3_OP_FPA_TO_FP)
  {
    assert(children.size()==1);
    if (tft == bitcast)
    {
      return Builder->CreateBitCast(children[0]->codegen(),FloatingSMT::ToFloating(width));
    }
    else if (tft == tsigned)
    {
      return Builder->CreateSIToFP(children[0]->codegen(), FloatingSMT::ToFloating(width));
    }
    else if (tft == fpfp)
    {
      //may be the same, extension, or truncation
      FloatingSMT* child = (FloatingSMT*)children[0];
      if (width == child->width)
      {
        return child->codegen();
      }
      else if (width > child->width)
      {
        return Builder->CreateFPExt(child->codegen(),FloatingSMT::ToFloating(width));
      }
      else
      {
        return Builder->CreateFPTrunc(child->codegen(),FloatingSMT::ToFloating(width));
      }
    }
    else { throw std::out_of_range("Unsupported Z3 FP to FP operation"); }
  }
  else if (op == Z3_OP_FPA_FP)
  {
    Value * sign = Builder->CreateShl(Builder->CreateZExt(children[0]->codegen(), IntegerType::get(*TheContext,width)), ConstantInt::get(IntegerType::get(*TheContext, width), width-1));
    Value * exp = Builder->CreateShl(Builder->CreateZExt(children[1]->codegen(), IntegerType::get(*TheContext,width)), ConstantInt::get(IntegerType::get(*TheContext,width),sbits-1));
    children[2]->codegen()->dump();
    Value * sig = Builder->CreateZExt(children[2]->codegen(), IntegerType::get(*TheContext,width));

    sig->dump();

    return Builder->CreateBitCast(Builder->CreateOr(sign, Builder->CreateOr(exp, sig)), FloatingSMT::ToFloating(width));
  }
  else if (op == Z3_OP_FPA_NAN)
  {
    return ConstantFP::getNaN(FloatingSMT::ToFloating(width));
  }
  else if (op == Z3_OP_FPA_MINUS_INF)
  {
    return ConstantFP::getInfinity(FloatingSMT::ToFloating(width), true);
  }
  else if (op == Z3_OP_FPA_PLUS_INF)
  {
    return ConstantFP::getInfinity(FloatingSMT::ToFloating(width), false);
  }
  else if (op == Z3_OP_FPA_MINUS_ZERO)
  {
    return ConstantFP::getNegativeZero(FloatingSMT::ToFloating(width));
  }
  else if (op == Z3_OP_FPA_PLUS_ZERO)
  {
    //ConstantFP::getZero doesn't exist
    return Builder->CreateFNeg(ConstantFP::getNegativeZero(FloatingSMT::ToFloating(width)));
  }
  else if (op == Z3_OP_FPA_ABS)
  {
    assert(children.size()==1);
    std::vector<Value *> args;
    args.push_back(children[0]->codegen());

    Function * fun = Intrinsic::getDeclaration(TheModule.get(), Intrinsic::fabs, FloatingSMT::ToFloating(width));
    return Builder->CreateCall(fun,args);
  }
  else if (op == Z3_OP_FPA_NEG)
  {
    assert(children.size()==1);
    return Builder->CreateFNeg(children[0]->codegen());
  }
  else if (op == Z3_OP_FPA_ADD)
  {
    assert(children.size()==2);
    return Builder->CreateFAdd(children[0]->codegen(), children[1]->codegen());
  }
  else if (op == Z3_OP_FPA_SUB)
  {
    assert(children.size()==2);
    return Builder->CreateFSub(children[0]->codegen(), children[1]->codegen());
  }
  else if (op == Z3_OP_FPA_MUL)
  {
    assert(children.size()==2);
    return Builder->CreateFMul(children[0]->codegen(), children[1]->codegen());
  }
  else if (op == Z3_OP_FPA_DIV)
  {
    assert(children.size()==2);
    return Builder->CreateFDiv(children[0]->codegen(), children[1]->codegen());
  }
  else if (op == Z3_OP_FPA_REM)
  {
    assert(children.size()==2);
    return Builder->CreateFRem(children[0]->codegen(), children[1]->codegen());
  }
  else if (op == Z3_OP_FPA_FMA)
  {
    assert(children.size()==3);
    std::vector<Value *> args;
    args.push_back(children[0]->codegen());
    args.push_back(children[1]->codegen());
    args.push_back(children[2]->codegen());

    Function * fun = Intrinsic::getDeclaration(TheModule.get(), Intrinsic::fma, FloatingSMT::ToFloating(width));
    return Builder->CreateCall(fun,args);
  }
  else if (op == Z3_OP_FPA_SQRT)
  {
    assert(children.size()==1);
    std::vector<Value *> args;
    args.push_back(children[0]->codegen());

    Function * fun = Intrinsic::getDeclaration(TheModule.get(), Intrinsic::sqrt, FloatingSMT::ToFloating(width));
    return Builder->CreateCall(fun,args);
  }
  else if (op == Z3_OP_FPA_MIN)
  {
    assert(children.size()==2);
    std::vector<Value *> args;
    args.push_back(children[0]->codegen());
    args.push_back(children[1]->codegen());

    Function * fun = Intrinsic::getDeclaration(TheModule.get(), Intrinsic::minnum, FloatingSMT::ToFloating(width));
    return Builder->CreateCall(fun,args);
  }
  else if (op == Z3_OP_FPA_MAX)
  {
    assert(children.size()==2);
    std::vector<Value *> args;
    args.push_back(children[0]->codegen());
    args.push_back(children[1]->codegen());

    Function * fun = Intrinsic::getDeclaration(TheModule.get(), Intrinsic::maxnum, FloatingSMT::ToFloating(width));
    return Builder->CreateCall(fun,args);
  }
  else
  {
    children[0]->codegen()->dump();
    throw std::out_of_range("Unsupported floating point operation.");
  }
}



FloatingSMT* FloatingSMT::MakeFloatingSMT(std::map<std::string, Value *> variables, expr expression)
{
  if (!expression.is_fpa())
  {
    context c;
    throw SMTTypeBuilderException(expression.get_sort(),expression);
  }
  else if (expression.is_const() && variables[expression.to_string()]) //Variable case
  {
    return new VariableFloatingSMT(variables, expression);
  }
  else //Expression case (there are no fp constants)
  {
    return new ExprFloatingSMT(variables, expression);
  }
}



//===----------------------------------------------------------------------===//
// Bitvectors
//===----------------------------------------------------------------------===//

bool BitvectorSMT::IsSignedComparison(expr expression)
{
  Z3_decl_kind k = expression.decl().decl_kind();
  return k == Z3_OP_SLEQ || k == Z3_OP_SGEQ || k == Z3_OP_SLT || k == Z3_OP_SGT;
}
bool BitvectorSMT::IsUnsignedComparison(expr expression)
{
  Z3_decl_kind k = expression.decl().decl_kind();
  return k == Z3_OP_ULEQ || k == Z3_OP_UGEQ || k == Z3_OP_ULT || k == Z3_OP_UGT;
}
bool BitvectorSMT::IsComparison(expr expression)
{
  return expression.num_args() >= 1 && ((expression.arg(0).is_bv() && (expression.is_eq() || expression.is_distinct())) || BitvectorSMT::IsSignedComparison(expression) || BitvectorSMT::IsUnsignedComparison(expression));
}

Value * BitvectorSMT::LlIsZero(Value * val)
{
  return Builder->CreateICmpEQ(val,ConstantInt::get(val->getType(), 0));
}
Value * BitvectorSMT::LlIsNegative(Value * val)
{
  return Builder->CreateICmpSLT(val,ConstantInt::get(val->getType(), 0));
}
Value * BitvectorSMT::LlIsPositive(Value * val)
{
  return Builder->CreateICmpSGE(val,ConstantInt::get(val->getType(), 0));
}
Value * BitvectorSMT::LlURem(Value* left, Value* right)
{
  return Builder->CreateSelect(BitvectorSMT::LlIsZero(right),left,Builder->CreateURem(left,right));
}





ConstBitvectorSMT::ConstBitvectorSMT(std::map<std::string, Value *> t_variables, expr t_contents) : BitvectorSMT(t_variables, t_contents)
{
  value = contents.to_string().substr(2);
  //Either binary or hex representation for constants in SMT LIB
  assert(contents.to_string()[0] == '#' && (contents.to_string()[1] == 'b' || contents.to_string()[1] == 'x'));
  isBinary = contents.to_string()[1]=='b';
  width = contents.get_sort().bv_size();
}
Value * ConstBitvectorSMT::codegen()
{
  return ConstantInt::get(IntegerType::get(*TheContext, width), value, isBinary?2:16);
}


VariableBitvectorSMT::VariableBitvectorSMT(std::map<std::string, Value *> t_variables, expr t_contents) : BitvectorSMT(t_variables, t_contents)
{
  name = contents.to_string();
  width = contents.get_sort().bv_size();
}
Value * VariableBitvectorSMT::codegen()
{
    return variables[name];
}

ExprBitvectorSMT::ExprBitvectorSMT(std::map<std::string, Value *> t_variables, expr t_contents) : BitvectorSMT(t_variables, t_contents)
{
  op = contents.decl().decl_kind();
  width = contents.get_sort().bv_size();

  //special instructions with non-bitvector arguments
  if (op == Z3_OP_ITE)
  {
    children.push_back(BooleanSMT::MakeBooleanSMT(variables, contents.arg(0)));
    children.push_back(BitvectorSMT::MakeBitvectorSMT(variables, contents.arg(1)));
    children.push_back(BitvectorSMT::MakeBitvectorSMT(variables, contents.arg(2)));
  }
  else if (op == Z3_OP_FPA_TO_UBV || op == Z3_OP_FPA_TO_SBV)
  {
    FloatingSMT::CheckRM(contents.arg(0));
    children.push_back(FloatingSMT::MakeFloatingSMT(variables, contents.arg(1)));
  }
  else
  {
    unsigned argCnt = contents.num_args();
    for (unsigned i = 0; i < argCnt; i++)
    {
        children.push_back(BitvectorSMT::MakeBitvectorSMT(variables,contents.arg(i)));
    }
  }
  //Special operations paramaterized by integers (repeat can be infered from types)
  if (op == Z3_OP_EXTRACT)
  {
    params.push_back(contents.hi());
    params.push_back(contents.lo());
  }
  else if (op == Z3_OP_ROTATE_LEFT || op == Z3_OP_ROTATE_RIGHT)
  {
    context c;
    params.push_back(Z3_get_decl_int_parameter(c, contents.decl(),0));
  }
}

Value * ExprBitvectorSMT::codegen()
{
  if (op == Z3_OP_ITE)
  {
    assert(children.size()==3);
    return Builder->CreateSelect(children[0]->codegen(),children[1]->codegen(), children[2]->codegen());
  }
  else if (op == Z3_OP_FPA_TO_UBV)
  {
    assert(children.size()==1);
    return Builder->CreateFPToUI(children[0]->codegen(), IntegerType::get(*TheContext, width));
  }
  else if (op == Z3_OP_FPA_TO_SBV)
  {
    assert(children.size()==1);
    return Builder->CreateFPToSI(children[0]->codegen(), IntegerType::get(*TheContext, width));
  }
  else if (op == Z3_OP_BNEG)
  {
    assert(children.size()==1);
    Value * zero = ConstantInt::get(IntegerType::get(*TheContext, ((BitvectorSMT*)children[0])->width), 0);
    return Builder->CreateSub(zero,children[0]->codegen());
  }
  else if (op == Z3_OP_BADD)
  {
    assert(children.size()==2);
    return Builder->CreateAdd(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_BSUB)
  {
    assert(children.size()==2);
    return Builder->CreateSub(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_BMUL)
  {
    assert(children.size()==2);
    return Builder->CreateMul(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_BSDIV)
  {
    assert(children.size()==2);
    Value * one = ConstantInt::get(IntegerType::get(*TheContext, ((BitvectorSMT*)children[0])->width), 1);
    Value * mone = ConstantInt::get(IntegerType::get(*TheContext, ((BitvectorSMT*)children[0])->width), -1);
    return Builder->CreateSelect(BitvectorSMT::LlIsZero(children[1]->codegen()),Builder->CreateSelect(BitvectorSMT::LlIsNegative(children[0]->codegen()), one,mone),Builder->CreateSDiv(children[0]->codegen(),children[1]->codegen()));
  }
  else if (op == Z3_OP_BUDIV)
  {
    assert(children.size()==2);
    Value * mone = ConstantInt::get(IntegerType::get(*TheContext, ((BitvectorSMT*)children[0])->width), -1);
    return Builder->CreateSelect(BitvectorSMT::LlIsZero(children[1]->codegen()),mone,Builder->CreateUDiv(children[0]->codegen(),children[1]->codegen()));
  }
  else if (op == Z3_OP_BSREM)
  {
    assert(children.size()==2);
    return Builder->CreateSelect(BitvectorSMT::LlIsZero(children[1]->codegen()), children[0]->codegen(), Builder->CreateSRem(children[0]->codegen(), children[1]->codegen()));
  }
  else if (op == Z3_OP_BUREM)
  {
    assert(children.size()==2);
    return BitvectorSMT::LlURem(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_BSMOD)
  {
    assert(children.size()==2);
    Value * zero = ConstantInt::get(IntegerType::get(*TheContext, ((BitvectorSMT*)children[0])->width), 0);
    Value * s = children[0]->codegen();
    Value * t = children[1]->codegen();
    Value * u = BitvectorSMT::LlURem(Builder->CreateSelect(BitvectorSMT::LlIsNegative(s), Builder->CreateSub(zero,s),s), Builder->CreateSelect(BitvectorSMT::LlIsNegative(t), Builder->CreateSub(zero,t),t));

    Value * sel0 = Builder->CreateSelect(Builder->CreateAnd(BitvectorSMT::LlIsPositive(s),BitvectorSMT::LlIsNegative(t)), Builder->CreateAdd(u,t), Builder->CreateSub(zero,u));
    Value * sel1 = Builder->CreateSelect(Builder->CreateAnd(BitvectorSMT::LlIsNegative(s),BitvectorSMT::LlIsPositive(t)), Builder->CreateAdd(Builder->CreateSub(zero,u),t),sel0);
    Value * sel2 = Builder->CreateSelect(Builder->CreateAnd(BitvectorSMT::LlIsPositive(s),BitvectorSMT::LlIsPositive(t)), u, sel1);
    return Builder->CreateSelect(BitvectorSMT::LlIsZero(u), u, sel2);
  }
  else if (op == Z3_OP_BAND)
  {
    assert(children.size()==2);
    return Builder->CreateAnd(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_BOR)
  {
    assert(children.size()==2);
    return Builder->CreateOr(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_BNOT)
  {
    assert(children.size()==2);
    return Builder->CreateNot(children[0]->codegen());
  }
  else if (op == Z3_OP_BXOR)
  {
    assert(children.size()>1);
    Value* temp = children[0]->codegen();
    for (int i = 1; i < children.size(); i++)
    {
      temp = Builder->CreateXor(temp,children[i]->codegen());
    }
    return temp;
  }
  else if (op == Z3_OP_BNAND)
  {
    assert(children.size()==2);
    return Builder->CreateNot(Builder->CreateAnd(children[0]->codegen(), children[1]->codegen()));
  }
  else if (op == Z3_OP_BNOR)
  {
    assert(children.size()==2);
    return Builder->CreateNot(Builder->CreateOr(children[0]->codegen(), children[1]->codegen()));
  }
  else if (op == Z3_OP_BXNOR)
  {
    assert(children.size()==2);
    return Builder->CreateNot(Builder->CreateXor(children[0]->codegen(), children[1]->codegen()));
  }
  else if (op == Z3_OP_CONCAT)
  {
    assert(children.size()==2);
    Value * left = Builder->CreateZExt(children[0]->codegen(), IntegerType::get(*TheContext, width));
    Value * right = Builder->CreateZExt(children[1]->codegen(), IntegerType::get(*TheContext, width));
    Value * shifted = Builder->CreateShl(left, ConstantInt::get(IntegerType::get(*TheContext, width), ((BitvectorSMT*)children[1])->width));
    return Builder->CreateOr(right, shifted);
  }
  else if (op == Z3_OP_SIGN_EXT)
  {
    assert(children.size()==1);
    return Builder->CreateSExt(children[0]->codegen(), IntegerType::get(*TheContext, width));
  }
  else if (op == Z3_OP_ZERO_EXT)
  {
    assert(children.size()==1);
    return Builder->CreateZExt(children[0]->codegen(), IntegerType::get(*TheContext, width));
  }
  else if (op == Z3_OP_EXTRACT)
  {
    assert(children.size()==1);
    IntegerType* oldTp = IntegerType::get(*TheContext,((BitvectorSMT*)children[0])->width);
    IntegerType* newTp = IntegerType::get(*TheContext,params[0]-params[1]+1);
    return Builder->CreateTrunc(Builder->CreateLShr(children[0]->codegen(), ConstantInt::get(oldTp, params[1])),newTp);
  }
  else if (op == Z3_OP_REPEAT)
  {
    assert(children.size()==1);
    int oldWidth = ((BitvectorSMT*)children[0])->width;
    int times = width/oldWidth;
    assert(oldWidth*times == width && times > 0);
    Value* child = children[0]->codegen();
    if (times==1)
    {
      return child;
    }
    else
    {
      Value* current = Builder->CreateZExt(child,IntegerType::get(*TheContext,width));
      for (int i = 1; i < times; i++)
      {
        current = Builder->CreateOr(current,Builder->CreateShl(Builder->CreateZExt(child,IntegerType::get(*TheContext,width)), ConstantInt::get(IntegerType::get(*TheContext,width),i*oldWidth)));
      }
      return current;
    }
  }
  else if (op == Z3_OP_BCOMP)
  {
    assert(children.size()==2);
    return Builder->CreateICmpEQ(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_BSHL)
  {
    assert(children.size()==2);
    IntegerType * childType = IntegerType::get(*TheContext, ((BitvectorSMT*)children[0])->width);
    return Builder->CreateSelect(Builder->CreateICmpUGE(children[1]->codegen(), ConstantInt::get(childType,width)),ConstantInt::get(childType,0),Builder->CreateShl(children[0]->codegen(), children[1]->codegen()));
  }
  else if (op == Z3_OP_BLSHR)
  {
    assert(children.size()==2);
    IntegerType * childType = IntegerType::get(*TheContext, ((BitvectorSMT*)children[0])->width);
    return Builder->CreateSelect(Builder->CreateICmpUGE(children[1]->codegen(), ConstantInt::get(childType,width)),ConstantInt::get(childType,0),Builder->CreateLShr(children[0]->codegen(), children[1]->codegen()));
  }
  else if (op == Z3_OP_BASHR)
  {
    assert(children.size()==2);
    IntegerType * childType = IntegerType::get(*TheContext, ((BitvectorSMT*)children[0])->width);
    Value* bad = Builder->CreateSelect(BitvectorSMT::LlIsNegative(children[0]->codegen()), ConstantInt::get(childType,-1), ConstantInt::get(childType, 0));
    return Builder->CreateSelect(Builder->CreateICmpUGE(children[1]->codegen(), ConstantInt::get(childType,width)),bad,Builder->CreateAShr(children[0]->codegen(),children[1]->codegen()));
  }
  else if (op == Z3_OP_ROTATE_LEFT)
  {
    assert(children.size()==1);

    IntegerType * ity = IntegerType::get(*TheContext, width);
    Value * child = children[0]->codegen();

    std::vector<Value *> args;
    args.push_back(child);
    args.push_back(child);
    args.push_back(ConstantInt::get(ity, params[0]%width));

    Function * fun = Intrinsic::getDeclaration(TheModule.get(), Intrinsic::fshl, ity);
    return Builder->CreateCall(fun,args);
  }
  else if (op == Z3_OP_ROTATE_RIGHT)
  {
    assert(children.size()==1);

    IntegerType * ity = IntegerType::get(*TheContext, width);
    Value * child = children[0]->codegen();

    std::vector<Value *> args;
    args.push_back(child);
    args.push_back(child);
    args.push_back(ConstantInt::get(ity, params[0]%width));

    Function * fun = Intrinsic::getDeclaration(TheModule.get(), Intrinsic::fshr, ity);
    return Builder->CreateCall(fun,args);
  }
  else
  {
    throw std::out_of_range("Unsupported bitvector opration.");
  }
}

BitvectorSMT* BitvectorSMT::MakeBitvectorSMT(std::map<std::string, Value *> variables, expr expression)
{
  if (!expression.is_bv())
  {
    context c;
    throw SMTTypeBuilderException(expression.get_sort(),expression);
  }
  else if (expression.is_const() && variables[expression.to_string()]) //Variable case
  {
    return new VariableBitvectorSMT(variables, expression);
  }
  else if (expression.is_const()) //Constant case
  {
    return new ConstBitvectorSMT(variables, expression);
  }
  else //Expression case
  {
    return new ExprBitvectorSMT(variables, expression);
  }
}

//===----------------------------------------------------------------------===//
// Booleans
//===----------------------------------------------------------------------===//

ConstBooleanSMT::ConstBooleanSMT(std::map<std::string, Value *> t_variables, expr t_contents) : BooleanSMT(t_variables, t_contents)
{
  value = contents.is_true();
}
Value * ConstBooleanSMT::codegen()
{
    return ConstantInt::getBool(*TheContext, value);
}

class VariableBooleanSMT : public BooleanSMT 
{
  std::string name;
  
  public:
    VariableBooleanSMT(std::map<std::string, Value *> t_variables, expr t_contents);
    Value * codegen() override;
};
VariableBooleanSMT::VariableBooleanSMT(std::map<std::string, Value *> t_variables, expr t_contents) : BooleanSMT(t_variables, t_contents)
{
  name = contents.to_string();
}
Value * VariableBooleanSMT::codegen()
{
    return variables[name];
}

ExprBooleanSMT::ExprBooleanSMT(std::map<std::string, Value *> t_variables, expr t_contents) : BooleanSMT(t_variables, t_contents)
{
  //Boolean only
  op = contents.decl().decl_kind();

  unsigned argCnt = contents.num_args();
  for (unsigned i = 0; i < argCnt; i++)
  {
    if (IntegerSMT::IsComparison(contents))
    {
      if (!isInteger) {throw NotIntegerException(contents.to_string());}
      children.push_back(IntegerSMT::MakeIntegerSMT(variables,contents.arg(i)));
      childCategory = integer;
    }
    else if (BitvectorSMT::IsComparison(contents)) //Bitvector arguments
    {
      if (isInteger) {throw NotIntegerException(contents.to_string());}
      children.push_back(BitvectorSMT::MakeBitvectorSMT(variables,contents.arg(i)));
      childCategory = bitvector;
    }
    else if (FloatingSMT::IsComparison(contents) || FloatingSMT::IsClassCheck(contents)) //Floating arguments
    {
      if (isInteger) {throw NotIntegerException(contents.to_string());}
      children.push_back(FloatingSMT::MakeFloatingSMT(variables,contents.arg(i)));
      childCategory = floating;
    }
    else //Boolean arguments
    {
      children.push_back(BooleanSMT::MakeBooleanSMT(variables,contents.arg(i)));
      childCategory = boolean;
    }
  }
}
Value * ExprBooleanSMT::codegen()
{
  //Boolean ops
  if (op == Z3_OP_NOT)
  {
    assert(children.size()==1);
    return Builder->CreateNot(children[0]->codegen());
  }
  else if (op == Z3_OP_AND)
  {
    Value* temp = children[0]->codegen();
    for (int i = 1; i < children.size(); i++)
    {
      temp = Builder->CreateAnd(temp,children[i]->codegen());
    }
    return temp;
  }
  else if (op == Z3_OP_OR)
  {
    Value* temp = children[0]->codegen();
    for (int i = 1; i < children.size(); i++)
    {
      temp = Builder->CreateOr(temp,children[i]->codegen());
    }
    return temp;
  }
  else if (op == Z3_OP_XOR)
  {
    Value* temp = children[0]->codegen();
    for (int i = 1; i < children.size(); i++)
    {
      temp = Builder->CreateXor(temp,children[i]->codegen());
    }
    return temp;
  }
  else if (op == Z3_OP_IMPLIES)
  {
    assert(children.size()==2);
    return Builder->CreateOr(Builder->CreateNot(children[0]->codegen()),children[1]->codegen());
  }
  //Integer comparisons
  else if (op == Z3_OP_LE)
  {
    return Builder->CreateICmpSLE(children[0]->codegen(), children[1]->codegen());
  }
  else if (op == Z3_OP_LT)
  {
    return Builder->CreateICmpSLT(children[0]->codegen(), children[1]->codegen());
  }
  else if (op == Z3_OP_GE)
  {
    return Builder->CreateICmpSGE(children[0]->codegen(), children[1]->codegen());
  }
  else if (op == Z3_OP_GT)
  {
    return Builder->CreateICmpSGT(children[0]->codegen(), children[1]->codegen());
  }
  //Bitvector comparisons
  else if (op == Z3_OP_SLEQ)
  {
    assert(children.size()==2);
    return Builder->CreateICmpSLE(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_SGEQ)
  {
    assert(children.size()==2);
    return Builder->CreateICmpSGE(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_SLT)
  {
    assert(children.size()==2);
    return Builder->CreateICmpSLT(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_SGT)
  {
    assert(children.size()==2);
    return Builder->CreateICmpSGT(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_ULEQ)
  {
    assert(children.size()==2);
    return Builder->CreateICmpULE(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_UGEQ)
  {
    assert(children.size()==2);
    return Builder->CreateICmpUGE(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_ULT)
  {
    assert(children.size()==2);
    return Builder->CreateICmpULT(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_UGT)
  {
    assert(children.size()==2);
    return Builder->CreateICmpUGT(children[0]->codegen(),children[1]->codegen());
  }
  else if (op == Z3_OP_ITE)
  {
    assert(children.size()==2);
    return Builder->CreateSelect(children[0]->codegen(),children[1]->codegen(),children[2]->codegen());
  }
  //Floating comparisons. All comparisons are ordered
  //(SMT LIB says comparison is false if either argument is NAN)
  else if (op == Z3_OP_FPA_EQ)
  {
    assert(children.size()==2);
    return Builder->CreateFCmpOEQ(children[0]->codegen(), children[1]->codegen());
  }
  else if (op == Z3_OP_FPA_LT)
  {
    assert(children.size()==2);
    return Builder->CreateFCmpOLT(children[0]->codegen(), children[1]->codegen());
  }
  else if (op == Z3_OP_FPA_GT)
  {
    assert(children.size()==2);
    return Builder->CreateFCmpOGT(children[0]->codegen(), children[1]->codegen());
  }
  else if (op == Z3_OP_FPA_LE)
  {
    assert(children.size()==2);
    return Builder->CreateFCmpOLE(children[0]->codegen(), children[1]->codegen());
  }
  else if (op == Z3_OP_FPA_GE)
  {
    assert(children.size()==2);
    return Builder->CreateFCmpOGE(children[0]->codegen(), children[1]->codegen());
  }
  //Floating point class check (7 differnt ops)
  else if (FloatingSMT::IsClassCheck(op))
  {
    assert(children.size()==1);
    return FloatingSMT::LlClass(children[0]->codegen(),op);
  }
  //Ambiguous
  else if (op == Z3_OP_EQ)
  {
    assert(children.size()==2);
    if (childCategory == boolean || childCategory == bitvector || childCategory == integer)
    {
      return Builder->CreateICmpEQ(children[0]->codegen(),children[1]->codegen());
    }
    else if (childCategory == floating)
    {
      IntegerType * iType = IntegerType::get(*TheContext,((FloatingSMT*)children[0])->width);
      Value* left = children[0]->codegen();
      Value* right = children[1]->codegen();
      //Both NAN or have the same bits
      return Builder->CreateOr(Builder->CreateAnd(FloatingSMT::LlClass(left, Z3_OP_FPA_IS_NAN), FloatingSMT::LlClass(right, Z3_OP_FPA_IS_NAN)), Builder->CreateICmpEQ(Builder->CreateBitCast(left, iType), Builder->CreateBitCast(right, iType)));
    }
    else
    {
      throw std::out_of_range("SMT = operation with unsupported child type.");
    }
  }
  else if (op == Z3_OP_DISTINCT)
  {
    if (children.size() < 2)
    {
      throw SMTUnsupportedOperationException("distinct with less than 2 arguments", contents);
    }
    else if (children.size() == 2)
    {
      if (childCategory == boolean || childCategory == bitvector || childCategory == integer)
      {
        return Builder->CreateICmpNE(children[0]->codegen(),children[1]->codegen());
      }
      else if (childCategory == floating)
      {
        return FloatingSMT::LlFNE(((FloatingSMT*)children[0])->width, children[0]->codegen(), children[1]->codegen());
      }
      else
      {
        throw std::out_of_range("SMT distinct operation with unsupported child type.");
      }
    }
    else
    {
      //Need to check pairwise inequality for all pairs
      Value* temp = 0; //  = ConstantInt::getTrue(*TheContext);
      for (int i = 0; i < children.size(); i++)
      {
        for (int j = i+1; j < children.size(); j++)
        {
          if (temp)
          {
            if (childCategory == boolean || childCategory == bitvector || childCategory == integer)
            {
              temp = Builder->CreateAnd(temp,Builder->CreateICmpNE(children[i]->codegen(),children[j]->codegen()));
            }
            else if (childCategory == floating)
            {
              temp = Builder->CreateAnd(temp,FloatingSMT::LlFNE(((FloatingSMT*)children[0])->width, children[i]->codegen(), children[j]->codegen()));
            }
          }
          else
          {
            if (childCategory == boolean || childCategory == bitvector || childCategory == integer)
            {
              temp = Builder->CreateICmpNE(children[i]->codegen(),children[j]->codegen());
            }
            else if (childCategory == floating)
            {
              temp = FloatingSMT::LlFNE(((FloatingSMT*)children[0])->width, children[i]->codegen(), children[j]->codegen());
            }
          }
        }
      }
      return temp;
    }
  }
  else
  {
    throw std::out_of_range("Unsupported boolean operation.");
  }
}


BooleanSMT* BooleanSMT::MakeBooleanSMT(std::map<std::string, Value *> variables, expr expression)
{
  if (!expression.is_bool())
  {
    context c;
    throw SMTTypeBuilderException(c.bool_sort(),expression);
  }
  else if (expression.is_const() && variables[expression.to_string()]) //Variable case
  {
    return new VariableBooleanSMT(variables, expression);
  }
  else if (expression.is_const()) //Constant case
  {
    return new ConstBooleanSMT(variables, expression);
  }
  else //Expression case
  {
    return new ExprBooleanSMT(variables, expression);
  }
}

//===----------------------------------------------------------------------===//
// Top level constraint
//===----------------------------------------------------------------------===//

ConstraintSMT::ConstraintSMT(std::string t_string) : string(t_string), contents(*(new context()))
{

  //Regular expression matching to get variables
  std::string s = t_string;
  std::smatch m;
  std::regex e (R"(\((declare-fun\s(\|.*\||[\~\!\@\$\%\^\&\*_\-\+\=\<\>\.\?\/A-Za-z0-9]+)\s*\(\s*\)\s*(\(\s*_\s*FloatingPoint\s*(\d+)\s*(\d+)\s*\)|Float16|Float32|Float64|Float128|FPN|Int|Bool|\(\s*_\s*BitVec\s*(\d+)\s*\))\s*|declare-const\s(\|.*\||[\~\!\@\$\%\^\&\*_\-\+\=\<\>\.\?\/A-Za-z0-9]+)\s*(\(\s*_\s*FloatingPoint\s*(\d+)\s*(\d+)\s*\)|Float16|Float32|Float64|Float128|FPN|Int|Bool|\(\s*_\s*BitVec\s*(\d+)\s*\))\s*)\))");

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
      types.push_back(Type::getInt1Ty(*TheContext));
    }
    else if (m[3]=="Int" || m[8] == "Int")
    {

      if (!isInteger) {throw NotIntegerException(m[0]);}
      types.push_back(Type::getIntNTy(*TheContext,integerWidth));
    }
    else if (m[6] != "") //Bitvector
    {
      if (isInteger) {throw NotIntegerException(m[0]);}
      types.push_back(Type::getIntNTy(*TheContext,stoi(m[6].str())));
    }
    else if (m[11] != "")
    {
      if (isInteger) {throw NotIntegerException(m[0]);}
      types.push_back(Type::getIntNTy(*TheContext,stoi(m[11].str())));
    }
    else if (m[4] != "" && m[5] != "") //General floating point
    {
      if (isInteger) {throw NotIntegerException(m[0]);}
      types.push_back(FloatingSMT::ToFloating(stoi(m[4])+stoi(m[5])));
    }
    else if (m[9] != "" && m[10] != "") 
    {
      if (isInteger) {throw NotIntegerException(m[0]);}
      types.push_back(FloatingSMT::ToFloating(stoi(m[9])+stoi(m[10])));
    }
    else if (m[3]=="Float16" || m[3]=="Float32" || m[3]=="Float64" || m[3]=="Float128") //Named floating points
    {
      if (isInteger) {throw NotIntegerException(m[0]);}
      types.push_back(FloatingSMT::ToFloating(stoi(m[3].str().substr(5))));
    }
    else if (m[8]=="Float16" || m[8]=="Float32" || m[8]=="Float64" || m[8]=="Float128") //Named floating points
    {
      if (isInteger) {throw NotIntegerException(m[0]);}
      types.push_back(FloatingSMT::ToFloating(stoi(m[8].str().substr(5))));
    }
    else if (m[3]=="FPN" || m[8]=="FPN") //Special case for the convention (define-sort FPN () (_ FloatingPoint 11 53)) in QF_FP
    {
      if (isInteger) {throw NotIntegerException(m[0]);}
      types.push_back(FloatingSMT::ToFloating(64));
    }
    else
    {
      throw SMTUnsupportedTypeException(m[3]);
    }
    s = m.suffix().str();
  }

  FunctionType* fnty = FunctionType::get(Type::getInt1Ty(*TheContext),types,false);
  fun = Function::Create(fnty, Function::ExternalLinkage, "SMT", TheModule.get());
  int i = 0;
  for (auto &arg : fun->args())
  {
    arg.setName(names[i]);
    variables[names[i]] = &arg;
    i++;
  }

  context c;

  contents = c.parse_string(t_string.c_str());

  for (expr e : contents)
  {
    assertions.push_back(BooleanSMT::MakeBooleanSMT(variables, e));
  }

}
Value* ConstraintSMT::codegen() {

  BasicBlock *bb = BasicBlock::Create(*TheContext, "b", fun);
  Builder->SetInsertPoint(bb);

  Value* temp = assertions[0]->codegen();
  if (assertions.size() > 1)
  {
    for (int i = 1; i < assertions.size(); i++)
    {
      temp = Builder->CreateAnd(temp,assertions[i]->codegen());
    }
  }

  Builder->CreateRet(temp);

  return fun;
}

//===----------------------------------------------------------------------===//
// Backend translation
//===----------------------------------------------------------------------===//
static solver BuildSMT(Function * fun);
static expr ToSMT(context* c, std::map<std::string, expr> variables, Value* val);
static expr ToSMTInteger(context* c, std::map<std::string, expr> variables, Value* val);
static z3::sort FpTypeToSort(context* c, Type* type);
static int FpTypeWidth(Type* type);
static expr ToSMTConstant(context* c, std::map<std::string, expr> variables, Constant* val);
static expr ToSMTIntrinsic(context* c, std::map<std::string, expr> variables, CallInst* val);



static void BuildSMT(context* c, solver* s, Function * fun)
{
  std::map<std::string, expr> variables;

  c->set_rounding_mode(RNE);


  for (Argument* arg = fun->arg_begin(); arg < fun->arg_end(); arg++)
  {
    if (arg->getType()->isIntegerTy())
    {
      //1-wide integer --> boolean
      if (arg->getType()->getIntegerBitWidth() == 1)
      {
        variables.insert(make_pair(arg->getName().str(), c->bool_const(arg->getName().str().c_str())));
      }
      else
      {
        if (isInteger)
        {
          //Reinterpret LLVM integers as SMT integers
          variables.insert(make_pair(arg->getName().str(), c->int_const(arg->getName().str().c_str())));
        }
        else
        {
          //Regular bitvector case
          variables.insert(make_pair(arg->getName().str(), c->bv_const(arg->getName().str().c_str(),arg->getType()->getIntegerBitWidth())));
          
        }
      }
    }
    else if (isInteger)
    {
      std::string type_str;
      llvm::raw_string_ostream rso(type_str);
      arg->print(rso);
      throw NotIntegerException(rso.str());
    }
    else if (arg->getType()->isHalfTy())
    {
      variables.insert(make_pair(arg->getName().str(), c->fpa_const(arg->getName().str().c_str(), 5, 11)));
    }
    else if (arg->getType()->isFloatTy())
    {
      variables.insert(make_pair(arg->getName().str(), c->fpa_const(arg->getName().str().c_str(), 8, 24)));
    }
    else if (arg->getType()->isDoubleTy())
    {
      variables.insert(make_pair(arg->getName().str(), c->fpa_const(arg->getName().str().c_str(), 11, 53)));
    }
    else if (arg->getType()->isFP128Ty())
    {
      variables.insert(make_pair(arg->getName().str(), c->fpa_const(arg->getName().str().c_str(), 15, 113)));
    }
    else
    {
      std::string type_str;
      llvm::raw_string_ostream rso(type_str);
      arg->print(rso);
      throw LLVMUnsupportedException("argument type", rso.str());
    }

  }

  expr res = ToSMT(c, variables, ((ReturnInst*)fun->getEntryBlock().getTerminator())->getOperand(0));

  s->add(res);

  return;
}


static expr ToSMT(context* c, std::map<std::string, expr> variables, Value* val)
{
        std::string type_str;
        llvm::raw_string_ostream rso(type_str);
        val->print(rso);

  if (isInteger) //Catch generic calls that should be for integer constraints
  {
    return ToSMTInteger(c,variables,val);
  }
  //Assumes isInteger == false
  else if (isa<Argument>(val))
  {
    return variables.at(val->getName().str());
  }
  else if (isa<Constant>(val))
  {
    return ToSMTConstant(c, variables, ((Constant*)val));
  }
  else if (isa<Instruction>(val)) //Instructions
  {
    Instruction* uv = ((Instruction*)val);
    //LLVM Intrinsic case
    if (uv->getOpcode()==Instruction::Call)
    {
      return ToSMTIntrinsic(c, variables, ((CallInst*)uv));
    }
    //Special case: umul.with.overflow followed by extract value
    else if (uv->getOpcode()==Instruction::ExtractValue)
    {
      Value* child = uv->getOperand(0);
      if (isa<CallInst>(child) && ((CallInst*)child)->getCalledFunction()->getIntrinsicID()==Intrinsic::umul_with_overflow)
      {
        expr left = ToSMT(c, variables, ((CallInst*)child)->getOperand(0));
        expr right = ToSMT(c, variables, ((CallInst*)child)->getOperand(1));
        expr zero = (*c).bv_val(0,left.get_sort().bv_size());
        return ite(((left == zero) || (right == zero)),(*c).bool_val(false),!(((left*right)/left)==right));
      }
      else
      {
        std::string type_str;
        llvm::raw_string_ostream rso(type_str);
        val->print(rso);
        throw LLVMUnsupportedException("vector operation extractvalue", rso.str());
      }
    }
    //Unary floating instructions
    else if (uv->getOpcode()==Instruction::FNeg)
    {
      //Z3 api redefines operators
      return -ToSMT(c, variables, uv->getOperand(0));
    }
    else if (uv->getOpcode()==Instruction::FPToUI)
    {
      return fpa_to_ubv(ToSMT(c, variables, uv->getOperand(0)), FpTypeWidth(uv->getType()));
    }
    else if (uv->getOpcode()==Instruction::FPToSI)
    {
      return fpa_to_sbv(ToSMT(c, variables, uv->getOperand(0)), FpTypeWidth(uv->getType()));
    }
    else if (uv->getOpcode()==Instruction::FPExt || uv->getOpcode()==Instruction::FPTrunc)
    {
      return fpa_to_fpa(ToSMT(c, variables, uv->getOperand(0)), FpTypeToSort(c, uv->getType()));
    }
    else if (uv->getOpcode()==Instruction::SIToFP)
    {
      return sbv_to_fpa(ToSMT(c, variables, uv->getOperand(0)), FpTypeToSort(c, uv->getType()));
    }
    else if (uv->getOpcode()==Instruction::UIToFP)
    {
      return ubv_to_fpa(ToSMT(c, variables, uv->getOperand(0)), FpTypeToSort(c, uv->getType()));
    }
    //Unary bitvector instructions
    else if (uv->getOpcode()==Instruction::BitCast)
    {
      if(uv->getType()->isFloatingPointTy())
      {
        return ToSMT(c, variables, uv->getOperand(0)).mk_from_ieee_bv(FpTypeToSort(c, uv->getType()));
      }
      else
      {
        //There is no floating to bitvector bitcast equivalent in SMT since NaN has multiple representations
        //Make a new variable and constrain it equal
        std::string type_str;
        llvm::raw_string_ostream rso(type_str);
        val->print(rso);
        throw LLVMUnsupportedException("floating point to bitvector bitcast", rso.str());
      }
    }
    else if (uv->getOpcode()==Instruction::Trunc)
    {
      return ToSMT(c, variables, uv->getOperand(0)).extract(uv->getType()->getIntegerBitWidth()-1, 0);
    }
    else if (uv->getOpcode()==Instruction::ZExt)
    {
      expr arg = ToSMT(c, variables, uv->getOperand(0));
      if (arg.is_bool())
      {
        //The optimizer may introduce zext i1 ...
        return zext(ite(arg, (*c).bv_val(1,1), (*c).bv_val(0,1)), uv->getType()->getIntegerBitWidth()-1);
      }
      else
      {
        return zext(arg, uv->getType()->getIntegerBitWidth()-arg.get_sort().bv_size());
      }      
    }
    else if (uv->getOpcode()==Instruction::SExt)
    {
      expr arg = ToSMT(c, variables, uv->getOperand(0));
      if (arg.is_bool())
      {
        //The optimizer may introduce sext i1 ...
        return sext(ite(arg, (*c).bv_val(1,1), (*c).bv_val(0,1)), uv->getType()->getIntegerBitWidth()-1);
      }
      else
      {
        return sext(arg, uv->getType()->getIntegerBitWidth()-arg.get_sort().bv_size());
      }      
    }
    else if (uv->getOpcode()==Instruction::Freeze)
    {
      //Frontend guarantees no undefined behavior, so freeze always returns its argument
      return ToSMT(c, variables, uv->getOperand(0));
    }
    //Binary instructions (boolean or bitvector)
    else if (uv->getOpcode()==Instruction::And)
    {
      expr left = ToSMT(c, variables, uv->getOperand(0));
      expr right = ToSMT(c, variables, uv->getOperand(1));
      return left.is_bool() ? (left && right) : (left & right);
    }
    else if (uv->getOpcode()==Instruction::Or)
    {
      expr left = ToSMT(c, variables, uv->getOperand(0));
      expr right = ToSMT(c, variables, uv->getOperand(1));
      return left.is_bool() ? (left || right) : (left | right);
    }
    else if (uv->getOpcode()==Instruction::Xor)
    {
      expr left = ToSMT(c, variables, uv->getOperand(0));
      expr right = ToSMT(c, variables, uv->getOperand(1));
      //The type check is built into the z3 ^ operator overload
      return left ^ right;
    }
    else if (uv->getOpcode()==Instruction::ICmp)
    {
      ICmpInst* vi = ((ICmpInst*)uv);
      
      //Operator overloads for EQ and NE work for both booleans and integers
      if (vi->getPredicate()==CmpInst::ICMP_EQ)
      {
        //This arose from a floating point = comparison. Important since there is no floating point to bitvector bitcast in SMT
        if (isa<BitCastInst>(vi->getOperand(0)) && isa<BitCastInst>(vi->getOperand(1)))
        {
          expr left = ToSMT(c, variables, ((BitCastInst*)(vi->getOperand(0)))->getOperand(0));
          expr right = ToSMT(c, variables, ((BitCastInst*)(vi->getOperand(1)))->getOperand(0));
          return left == right;
        }
        else if (isa<BitCastInst>(vi->getOperand(0)))
        {
          expr left = ToSMT(c, variables, ((BitCastInst*)(vi->getOperand(0)))->getOperand(0));
          expr right = ToSMT(c, variables, vi->getOperand(1)).mk_from_ieee_bv(left.get_sort());
          return left == right;
        }
        else if (isa<BitCastInst>(vi->getOperand(1)))
        {
          //Reverse order so we can do right.get_sort()
          expr right = ToSMT(c, variables, ((BitCastInst*)(vi->getOperand(1)))->getOperand(0));
          expr left = ToSMT(c, variables, vi->getOperand(0)).mk_from_ieee_bv(right.get_sort());
          return left == right;
        }
        else
        { //Regular case
          expr left = ToSMT(c, variables, vi->getOperand(0));
          expr right = ToSMT(c, variables, vi->getOperand(1));
          return left == right;
        }
      }
      else if (vi->getPredicate()==CmpInst::ICMP_NE)
      {
        //This arose from a floating point distinct comparison. Important since there is no floating point to bitvector bitcast in SMT
        if (isa<BitCastInst>(vi->getOperand(0)) && isa<BitCastInst>(vi->getOperand(1)))
        {
          expr left = ToSMT(c, variables, ((BitCastInst*)(vi->getOperand(0)))->getOperand(0));
          expr right = ToSMT(c, variables, ((BitCastInst*)(vi->getOperand(0)))->getOperand(0));
          return left != right;
        }
        else if (isa<BitCastInst>(vi->getOperand(0)))
        {
          expr left = ToSMT(c, variables, ((BitCastInst*)(vi->getOperand(0)))->getOperand(0));
          expr right = ToSMT(c, variables, vi->getOperand(1)).mk_from_ieee_bv(left.get_sort());
          return left != right;
        }
        else if (isa<BitCastInst>(vi->getOperand(1)))
        {
          //Reverse order so we can do right.get_sort()
          expr right = ToSMT(c, variables, ((BitCastInst*)(vi->getOperand(0)))->getOperand(0));
          expr left = ToSMT(c, variables, vi->getOperand(0)).mk_from_ieee_bv(right.get_sort());
          return left != right;
        }
        else
        {
          expr left = ToSMT(c, variables, vi->getOperand(0));
          expr right = ToSMT(c, variables, vi->getOperand(1));
          return left != right;
        }
      }
      else
      {
        //Can evaluate the children regularly
        expr left = ToSMT(c, variables, vi->getOperand(0));
        expr right = ToSMT(c, variables, vi->getOperand(1));
        if (vi->getPredicate()==CmpInst::ICMP_SGT)
        {
          return left > right;
        }
        else if (vi->getPredicate()==CmpInst::ICMP_SGE)
        {
          return left >= right;
        }
        else if (vi->getPredicate()==CmpInst::ICMP_SLT)
        {
          return left < right;
        }
        else if (vi->getPredicate()==CmpInst::ICMP_SLE)
        {
          return left <= right;
        }
        else if (vi->getPredicate()==CmpInst::ICMP_UGT)
        {
          return ugt(left,right);
        }
        else if (vi->getPredicate()==CmpInst::ICMP_UGE)
        {
          return uge(left,right);
        }
        else if (vi->getPredicate()==CmpInst::ICMP_ULT)
        {
          return ult(left,right);
        }
        else if (vi->getPredicate()==CmpInst::ICMP_ULE)
        {
          return ule(left,right);
        }
        else { throw std::out_of_range("Unsupported ICMP instruction predicate."); }
      }
    }
    //Binary bitvector instructions
    else if (uv->getOpcode()==Instruction::Shl)
    {
      expr left = ToSMT(c, variables, uv->getOperand(0));
      expr right = ToSMT(c, variables, uv->getOperand(1));
      //Check for shift left by a constant; this can be replaced with multiplication
      int rr;
      if (shiftToMultiply && right.is_const() && ((rr = std::atoi(right.to_string().c_str())) > 0))
      {
        int i = 1;
        while (rr > 0) { i*=2; rr--;}
        return left * (*c).bv_val(i,uv->getType()->getIntegerBitWidth());
      }
      else
      {
        return shl(left,right);
      }
    }
    else if (uv->getOpcode()==Instruction::LShr)
    {
      expr left = ToSMT(c, variables, uv->getOperand(0));
      expr right = ToSMT(c, variables, uv->getOperand(1));
      return lshr(left,right);
    }
    else if (uv->getOpcode()==Instruction::AShr)
    {
      expr left = ToSMT(c, variables, uv->getOperand(0));
      expr right = ToSMT(c, variables, uv->getOperand(1));
      return ashr(left,right);
    }
    else if (uv->getOpcode()==Instruction::UDiv)
    {
      expr left = ToSMT(c, variables, uv->getOperand(0));
      expr right = ToSMT(c, variables, uv->getOperand(1));
      return udiv(left,right);
    }
    else if (uv->getOpcode()==Instruction::URem)
    {
      expr left = ToSMT(c, variables, uv->getOperand(0));
      expr right = ToSMT(c, variables, uv->getOperand(1));
      return urem(left,right);
    }
    else if (uv->getOpcode()==Instruction::SRem)
    {
      expr left = ToSMT(c, variables, uv->getOperand(0));
      expr right = ToSMT(c, variables, uv->getOperand(1));
      return srem(left,right);
    }
    //Bitvector and floating instructions (double operator overload meaning)
    else if (uv->getOpcode()==Instruction::Add || uv->getOpcode()==Instruction::FAdd)
    {
      expr left = ToSMT(c, variables, uv->getOperand(0));
      expr right = ToSMT(c, variables, uv->getOperand(1));
      return left + right;
    }
    else if (uv->getOpcode()==Instruction::Sub || uv->getOpcode()==Instruction::FSub)
    {
      expr left = ToSMT(c, variables, uv->getOperand(0));
      expr right = ToSMT(c, variables, uv->getOperand(1));
      return left - right;
    }
    else if (uv->getOpcode()==Instruction::Mul || uv->getOpcode()==Instruction::FMul)
    {
      expr left = ToSMT(c, variables, uv->getOperand(0));
      expr right = ToSMT(c, variables, uv->getOperand(1));
      return left * right;
    }
    else if (uv->getOpcode()==Instruction::SDiv || uv->getOpcode()==Instruction::FDiv)
    {
      expr left = ToSMT(c, variables, uv->getOperand(0));
      expr right = ToSMT(c, variables, uv->getOperand(1));
      return left / right;
    }
    //Binary floating instructions
    else if (uv->getOpcode()==Instruction::FRem)
    {
      expr left = ToSMT(c, variables, uv->getOperand(0));
      expr right = ToSMT(c, variables, uv->getOperand(1));
      return rem(left,right);
    }
    else if (uv->getOpcode()==Instruction::FCmp)
    {
      FCmpInst* vi = ((FCmpInst*)uv);
      expr left = ToSMT(c, variables, vi->getOperand(0));
      expr right = ToSMT(c, variables, vi->getOperand(1));

      if (vi->getPredicate()==CmpInst::FCMP_FALSE)
      {
        return (*c).bool_val(false);
      }
      //Ordered (not both NaN, matches SMT semantics)
      else if (vi->getPredicate()==CmpInst::FCMP_OEQ)
      {
        return fp_eq(left, right);
      }
      else if (vi->getPredicate()==CmpInst::FCMP_OGT)
      {
        return left > right;
      }
      else if (vi->getPredicate()==CmpInst::FCMP_OGE)
      {
        return left >= right;
      }
      else if (vi->getPredicate()==CmpInst::FCMP_OLT)
      {
        return left < right;
      }
      else if (vi->getPredicate()==CmpInst::FCMP_OLE)
      {
        return left <= right;
      }
      else if (vi->getPredicate()==CmpInst::FCMP_ONE)
      {
        return (!left.mk_is_nan()) && (!right.mk_is_nan()) && (!fp_eq(left,right));
      }
      else if (vi->getPredicate()==CmpInst::FCMP_ORD)
      {
        return (!left.mk_is_nan()) && (!right.mk_is_nan());
      }
      //Unordered (either is NaN or the comparison)
      else if (vi->getPredicate()==CmpInst::FCMP_UEQ)
      {
        return left.mk_is_nan() || right.mk_is_nan() || fp_eq(left,right);
      }
      else if (vi->getPredicate()==CmpInst::FCMP_UGT)
      {
        return left.mk_is_nan() || right.mk_is_nan() || (left > right);
      }
      else if (vi->getPredicate()==CmpInst::FCMP_UGE)
      {
        return left.mk_is_nan() || right.mk_is_nan() || (left >= right);
      }
      else if (vi->getPredicate()==CmpInst::FCMP_ULT)
      {
        return left.mk_is_nan() || right.mk_is_nan() || (left < right);
      }
      else if (vi->getPredicate()==CmpInst::FCMP_ULE)
      {
        return left.mk_is_nan() || right.mk_is_nan() || (left <= right);
      }
      else if (vi->getPredicate()==CmpInst::FCMP_UNE)
      {
        return left.mk_is_nan() || right.mk_is_nan() || (!fp_eq(left, right));
      }
      else if (vi->getPredicate()==CmpInst::FCMP_UNO)
      {
        return left.mk_is_nan() || right.mk_is_nan();
      }
      else if (vi->getPredicate()==CmpInst::FCMP_TRUE)
      {
        return (*c).bool_val(true);
      }
      else { throw std::out_of_range("Unsupported FCMP predicate."); }
    }
    //Select instruction
    else if (uv->getOpcode()==Instruction::Select)
    {
      expr cond = ToSMT(c, variables, uv->getOperand(0));
      expr left = ToSMT(c, variables, uv->getOperand(1));
      expr right = ToSMT(c, variables, uv->getOperand(2));
      return ite(cond,left,right);
    }
    else
    {
      std::string type_str;
      llvm::raw_string_ostream rso(type_str);
      val->print(rso);
      throw LLVMUnsupportedException("floating point or bitvector instruction", rso.str());
    }
  }
  else
  {
    std::string type_str;
    llvm::raw_string_ostream rso(type_str);
    val->print(rso);
    throw LLVMUnsupportedException("must be an argument, constant, or instruction", rso.str());
  }
}


static expr ToSMTInteger(context* c, std::map<std::string, expr> variables, Value* val)
{
  if (!isInteger)
  {
    return ToSMT(c, variables, val);
  }
  //Assumes isInteger == true
  if (isa<Argument>(val))
  {
    return variables.at(val->getName().str());
  }
  else if (isa<Constant>(val))
  {
    return ToSMTConstant(c, variables, ((Constant*)val));
  }
  else if (isa<Instruction>(val)) //Instructions
  {
    Instruction* uv = ((Instruction*)val);
    //LLVM Intrinsic case
    if (uv->getOpcode()==Instruction::Call)
    {
      return ToSMTIntrinsic(c, variables, ((CallInst*)uv));
    }
    else if (uv->getOpcode()==Instruction::ZExt && uv->getOperand(0)->getType()->isIntegerTy(1))
    {
      expr arg = ToSMTInteger(c, variables, uv->getOperand(0));
      return ite(arg, (*c).int_val(1), (*c).int_val(0)); 
    }
    else if (uv->getOpcode()==Instruction::Freeze)
    {
      //Frontend guarantees no undefined behavior, so freeze always returns its argument
      return ToSMTInteger(c, variables, uv->getOperand(0));
    }
    //Binary instructions
    else if (uv->getOpcode()==Instruction::And && uv->getOperand(0)->getType()->isIntegerTy(1))
    {
      expr left = ToSMTInteger(c, variables, uv->getOperand(0));
      expr right = ToSMTInteger(c, variables, uv->getOperand(1));
      return left && right;
    }
    else if (uv->getOpcode()==Instruction::Or && uv->getOperand(0)->getType()->isIntegerTy(1))
    {
      expr left = ToSMTInteger(c, variables, uv->getOperand(0));
      expr right = ToSMTInteger(c, variables, uv->getOperand(1));
      return left || right;
    }
    else if (uv->getOpcode()==Instruction::Xor)
    {
      expr left = ToSMTInteger(c, variables, uv->getOperand(0));
      expr right = ToSMTInteger(c, variables, uv->getOperand(1));
      return left ^ right;
    }
    else if (uv->getOpcode()==Instruction::ICmp)
    {
      ICmpInst* vi = ((ICmpInst*)uv);
      expr left = ToSMTInteger(c, variables, vi->getOperand(0));
      expr right = ToSMTInteger(c, variables, vi->getOperand(1));
      //Operator overloads for EQ and NE work for both booleans and integers
      if (vi->getPredicate()==CmpInst::ICMP_EQ)
      {
        return left == right;
      }
      else if (vi->getPredicate()==CmpInst::ICMP_NE)
      {
        return left != right;
      }
      else if (vi->getPredicate()==CmpInst::ICMP_SGT)
      {
        return left > right;
      }
      else if (vi->getPredicate()==CmpInst::ICMP_SGE)
      {
        return left >= right;
      }
      else if (vi->getPredicate()==CmpInst::ICMP_SLT)
      {
        return left < right;
      }
      else if (vi->getPredicate()==CmpInst::ICMP_SLE)
      {
        return left <= right;
      }
      else
      { //No unsigned comparison for integers
        std::string type_str;
        llvm::raw_string_ostream rso(type_str);
        val->print(rso);
        throw NotIntegerException(rso.str());
      }
    }
    //Binary bitvector instructions
    else if (uv->getOpcode()==Instruction::Shl)
    {
      expr left = ToSMTInteger(c, variables, uv->getOperand(0));
      expr right = ToSMTInteger(c, variables, uv->getOperand(1));
      //Check for shift left by a constant; this is the only possible case for integers
      int rr;
      if (shiftToMultiply && right.is_const() && ((rr = std::atoi(right.to_string().c_str())) > 0))
      {
        int i = 1;
        while (rr > 0) { i*=2; rr--;}
        return left * (*c).int_val(i);
      }
      else
      {
        std::string type_str;
        llvm::raw_string_ostream rso(type_str);
        val->print(rso);
        throw NotIntegerException(rso.str());
      }
    }
    else if (uv->getOpcode()==Instruction::Add)
    {
      expr left = ToSMTInteger(c, variables, uv->getOperand(0));
      expr right = ToSMTInteger(c, variables, uv->getOperand(1));
      return left + right;
    }
    else if (uv->getOpcode()==Instruction::Sub)
    {
      expr left = ToSMTInteger(c, variables, uv->getOperand(0));
      expr right = ToSMTInteger(c, variables, uv->getOperand(1));
      return left - right;
    }
    else if (uv->getOpcode()==Instruction::Mul)
    {
      expr left = ToSMTInteger(c, variables, uv->getOperand(0));
      expr right = ToSMTInteger(c, variables, uv->getOperand(1));
      return left * right;
    }
    else if (uv->getOpcode()==Instruction::SDiv)
    {
      expr left = ToSMTInteger(c, variables, uv->getOperand(0));
      expr right = ToSMTInteger(c, variables, uv->getOperand(1));
      return left / right;
    }
    else if (uv->getOpcode()==Instruction::SRem)
    {
      expr left = ToSMTInteger(c, variables, uv->getOperand(0));
      expr right = ToSMTInteger(c, variables, uv->getOperand(1));
      return rem(left,right);
    }
    //Select instruction
    else if (uv->getOpcode()==Instruction::Select)
    {
      expr cond = ToSMTInteger(c, variables, uv->getOperand(0));
      expr left = ToSMTInteger(c, variables, uv->getOperand(1));
      expr right = ToSMTInteger(c, variables, uv->getOperand(2));
      return ite(cond,left,right);
    }
    else
    {
      std::string type_str;
      llvm::raw_string_ostream rso(type_str);
      val->print(rso);
      throw NotIntegerException(rso.str());
    }
  }
  else
  {
    std::string type_str;
    llvm::raw_string_ostream rso(type_str);
    val->print(rso);
    throw LLVMUnsupportedException("must be an argument, constant, or instruction", rso.str());
  }
}


static z3::sort FpTypeToSort(context* c, Type* type)
{
  if (type->isHalfTy())
  {
    return (*c).fpa_sort(5,11);
  }
  else if (type->isFloatTy())
  {
    return (*c).fpa_sort(8,24);
  }
  else if (type->isDoubleTy())
  {
    return (*c).fpa_sort(11,53);
  }
  else if (type->isFP128Ty())
  {
    return (*c).fpa_sort(15,113);
  }
  else
  {
    throw std::out_of_range("Unsupported floating point type while getting sort (only 16, 32, 64, and 128 supported).");
  }
}

static int FpTypeWidth(Type* type)
{
  if (type->isHalfTy())
  {
    return 16;
  }
  else if (type->isFloatTy())
  {
    return 32;
  }
  else if (type->isDoubleTy())
  {
    return 64;
  }
  else if (type->isFP128Ty())
  {
    return 128;
  }
  else
  {
    throw std::out_of_range("Unsupported floating point type while getting width (only 16, 32, 64, and 128 supported).");
  }
}

static expr ToSMTConstant(context* c, std::map<std::string, expr> variables, Constant* val)
{
  if (val->getType()->isIntegerTy())
  {
    if (val->getType()->getIntegerBitWidth()==1)
    {
      return (*c).bool_val(val->isOneValue());
    }
    else if (isInteger)
    {
      return (*c).int_val(toString(val->getUniqueInteger(),10,false).c_str());
    }
    else
    {
      return (*c).bv_val(toString(val->getUniqueInteger(),10,false).c_str(), val->getType()->getIntegerBitWidth());
    }
  }
  else if (isInteger)
  {
    std::string type_str;
    llvm::raw_string_ostream rso(type_str);
    val->print(rso);
    throw NotIntegerException(rso.str());
  }
  else if (val->getType()->isFloatingPointTy())
  {
    char* s;
    ((ConstantFP*)val)->getValue().convertToHexString(s, 0, true, RoundingMode::NearestTiesToEven);
    return (*c).bv_val(s, FpTypeWidth(val->getType())).mk_from_ieee_bv(FpTypeToSort(c,val->getType()));
  }
  else
  {
    std::string type_str;
    llvm::raw_string_ostream rso(type_str);
    val->print(rso);
    throw LLVMUnsupportedException("constant type", rso.str());
  }
}

static expr ToSMTIntrinsic(context* c, std::map<std::string, expr> variables, CallInst* val)
{
  Intrinsic::ID id = val->getCalledFunction()->getIntrinsicID();
  //Intrinsics which are resonable in the integer context
  if (id==Intrinsic::abs)
  {
    expr arg = ToSMT(c, variables, val->getOperand(0));
    if (isInteger)
    {
      return abs(arg);
    }
    else
    {
      return ite(arg < (*c).bv_val(0,FpTypeWidth(val->getType())), -arg, arg);
    }
  }
  else if (id==Intrinsic::smin)
  {
    expr left = ToSMT(c, variables, val->getOperand(0));
    expr right = ToSMT(c, variables, val->getOperand(1));
    return ite(left <= right,left,right);
  }
  else if (id==Intrinsic::smax)
  {
    expr left = ToSMT(c, variables, val->getOperand(0));
    expr right = ToSMT(c, variables, val->getOperand(1));
    return ite(left <= right,right,left);
  }
  else if (isInteger)
  {
    std::string type_str;
    llvm::raw_string_ostream rso(type_str);
    val->print(rso);
    throw NotIntegerException(rso.str());
  }
  //Not possible in the integer context
  else if (id==Intrinsic::fabs)
  {
    return z3::abs(ToSMT(c, variables, val->getOperand(0)));
  }
  else if (id==Intrinsic::fma)
  {
    return z3::fma(ToSMT(c, variables, val->getOperand(0)),ToSMT(c, variables, val->getOperand(1)),ToSMT(c, variables, val->getOperand(2)), (*c).fpa_rounding_mode());
  }
  else if (id==Intrinsic::sqrt)
  {
    return z3::sqrt(ToSMT(c, variables, val->getOperand(0)),(*c).fpa_rounding_mode());
  }
  else if (id==Intrinsic::minnum)
  {
    return min(ToSMT(c, variables, val->getOperand(0)),ToSMT(c, variables, val->getOperand(1)));
  }
  else if (id==Intrinsic::maxnum)
  {
    return max(ToSMT(c, variables, val->getOperand(0)),ToSMT(c, variables, val->getOperand(1)));
  }
  else if (id==Function::lookupIntrinsicID("llvm.is.fpclass"))
  {
    expr arg = ToSMT(c, variables, val->getOperand(0));
    int64_t bits = ((ConstantInt*)(val->getOperand(1)))->getSExtValue();
    if (bits==3)
    {
      return arg.mk_is_nan();
    }
    else if (bits==516)
    {
      return arg.mk_is_inf();
    }
    else if (bits==96)
    {
      return arg.mk_is_zero();
    }
    else if (bits==264)
    {
      return arg.mk_is_normal();
    }
    else if (bits==144)
    {
      return arg.mk_is_subnormal();
    }
    else if (bits==60)
    {
      return expr(*c,Z3_mk_fpa_is_negative(*c, arg));
    }
    else if (bits==960)
    {
      return expr(*c,Z3_mk_fpa_is_positive(*c, arg));
    }
    else
    {
      std::string type_str;
      llvm::raw_string_ostream rso(type_str);
      val->print(rso);
      throw LLVMUnsupportedException("floating point class check flags", rso.str());
    }
  }
  else if (id==Intrinsic::bswap)
  {
    //Reverse the order of bytes
    expr arg = ToSMT(c, variables, val->getOperand(0));
    int width = FpTypeWidth(val->getType());
    expr_vector v = expr_vector(*c);
    for (int i = (width/8)-1; i>=0; i--)
    {
      v.push_back(arg.extract(width-(8*i)-1, width-(8*(i+1))));
    }
    return concat(v);
  }
  else if (id==Intrinsic::ctpop)
  {
    //Count the number of 1 bits
    expr arg = ToSMT(c, variables, val->getOperand(0));
    int width = FpTypeWidth(val->getType());
    expr temp = arg.extract(0,0);
    for (int i = 1; i<width; i++)
    {
      temp = temp + arg.extract(i,i);
    }
    return temp;
  }
  else if (id==Intrinsic::bitreverse)
  {
    //Reverse the order of bits
    expr arg = ToSMT(c, variables, val->getOperand(0));
    int width = FpTypeWidth(val->getType());
    expr_vector v = expr_vector(*c);
    for (int i = width-1; i>=0; i++)
    {
      v.push_back(arg.extract(i,i));
    }
    return concat(v);
  }
  else if (id==Intrinsic::fshl)
  {
    //Funnel shift
    expr left = ToSMT(c, variables, val->getOperand(0));
    expr right = ToSMT(c, variables, val->getOperand(1));
    expr shamt = ToSMT(c, variables, val->getOperand(2));
    int width = FpTypeWidth(val->getType());
    return shl(concat(left, right), shamt).extract((width*2)-1, width);
  }
  else if (id==Intrinsic::fshr)
  {
    //Funnel shift
    expr left = ToSMT(c, variables, val->getOperand(0));
    expr right = ToSMT(c, variables, val->getOperand(1));
    expr shamt = ToSMT(c, variables, val->getOperand(2));
    int width = FpTypeWidth(val->getType());
    return lshr(concat(left,right),shamt).extract(width-1,0);
  }
  else if (id==Intrinsic::usub_sat)
  {
    //Subtraction without underflow (clamped to 0)
    expr left = ToSMT(c, variables, val->getOperand(0));
    expr right = ToSMT(c, variables, val->getOperand(1));
    return ite(ule(left,right),(*c).bv_val(0,FpTypeWidth(val->getType())),left-right);
  }
  else if (id==Intrinsic::uadd_sat)
  {
    //Addition without overflow (clamped to max, i.e. -1)
    expr left = ToSMT(c, variables, val->getOperand(0));
    expr right = ToSMT(c, variables, val->getOperand(1));
    return ite(ule(left+right,left),(*c).bv_val(-1,FpTypeWidth(val->getType())),left+right);
  }
  else if (id==Intrinsic::umin)
  {
    expr left = ToSMT(c, variables, val->getOperand(0));
    expr right = ToSMT(c, variables, val->getOperand(1));
    return ite(ule(left,right),left,right);
  }
  else if (id==Intrinsic::umax)
  {
    expr left = ToSMT(c, variables, val->getOperand(0));
    expr right = ToSMT(c, variables, val->getOperand(1));
    return ite(ule(left,right),right,left);
  }
  else
  {
    std::string type_str;
      llvm::raw_string_ostream rso(type_str);
      val->print(rso);
      throw LLVMUnsupportedException("intrinsic", rso.str());
  }  
}



//===----------------------------------------------------------------------===//
// Main
//===----------------------------------------------------------------------===//

static void InitializeModule(std::string name) {
  // Open a new context and module.
  TheContext = std::make_unique<LLVMContext>();
  TheModule = std::make_unique<Module>(name, *TheContext);

  // Create a new builder for the module.
  Builder = std::make_unique<IRBuilder<>>(*TheContext);
}


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
  std::cout << "things\n";
  std::cout << "things\n";
  std::cout << "things\n";

  shiftToMultiply = false;
  integerWidth = 64;
  isInteger = false;

  if(HasFlag(argc, argv, "-h"))
  {
    std::cout << "SLOT arguments:\n";
    std::cout << "   -h         : See help menu\n";
    std::cout << "   -s <file>  : The input SMTLIB2 format file (required)\n";
    std::cout << "   -o <file>  : The output file. If not provided, output is sent to stdout.\n";
    std::cout << "   -i         : The input constraint contains (only) SMTLIB integers. False by default.\n";
    std::cout << "   -w <size>  : The bitwidth with which to underapproximate integers. Default is 64.\n";
    std::cout << "   -m         : Convert constant shifts to multiplication.\n";
    return 0;
  }

  if (HasFlag(argc, argv, "-i"))
  {
    isInteger=true;
    if (HasFlag(argc, argv, "-w"))
    {
      integerWidth = std::stoi(GetFlag(argc,argv,"-w"));
    }
  }
  else if (HasFlag(argc, argv, "-w"))
  {
    std::cout << "-w flag is only valid if -i is specified.\n";
    return 1;
  }

  if (HasFlag(argc, argv, "-m"))
  {
    shiftToMultiply = true;
  }


  if(!HasFlag(argc, argv, "-s"))
  {
    std::cout << "Must specify input file with -s.\n";
    return 1;
  }
  char * inputFilename = GetFlag(argc, argv, "-s");
  if (!inputFilename)
  {
    std::cout << "Invalid input file name.\n";
    return 1;
  }

  InitializeModule(inputFilename);

  std::ifstream t(inputFilename);
  std::stringstream buffer;
  buffer << t.rdbuf();
  std::string smt_str = buffer.str();

  //Exceptions indicate unsupported instructions, floating point types, rounding modes, etc ...
  //If a translation cannot be performed, simply return the input constraint
  try
  {


    ConstraintSMT a = ConstraintSMT(smt_str);

    //Start frontend translation
    a.codegen();


    TheModule->getFunction("SMT")->print(outs());
/*
    PreservedAnalyses LazyValueInfoPrinterNPM::run(Function &F, FunctionAnalysisManager &AM) {
  auto *LVI = &AM.getResult<LazyValueAnalysis>(F);
  auto &DTree = AM.getResult<DominatorTreeAnalysis>(F);
  LVI->printLVI(F, DTree, dbgs());
  return PreservedAnalyses::all();
  }*/

      LoopAnalysisManager LAM;
      FunctionAnalysisManager FAM;
      CGSCCAnalysisManager CGAM;
      ModuleAnalysisManager MAM;

      PassBuilder PB;

      PB.registerModuleAnalyses(MAM);
      PB.registerCGSCCAnalyses(CGAM);
      PB.registerFunctionAnalyses(FAM);
      PB.registerLoopAnalyses(LAM);
      PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

      LazyValueAnalysis::Result* r = &FAM.getResult<LazyValueAnalysis>(*(TheModule->getFunction("SMT")));
      DominatorTreeAnalysis::Result& d = FAM.getResult<DominatorTreeAnalysis>(*(TheModule->getFunction("SMT")));

      Instruction* ret = TheModule->getFunction("SMT")->getEntryBlock().getTerminator();

      r->getConstantRange(ret->getOperand(0),ret).print(outs());
      std::cout << "\n\n";

      r->printLVI(*(TheModule->getFunction("SMT")),d,outs());

      std::cout << "-----------------\n";
      //exit(0);

    //End frontend translation




    bool usedInstCombine = false;
    bool usedAInstCombine = false;
    bool usedReassociate = false;
    bool usedSCCP = false;
    bool usedDCE = false;
    bool usedADCE = false;
    bool usedInstSimplify = false;
    bool usedGVN = false;

    if (HasFlag(argc, argv, "-p"))
    {


      LoopAnalysisManager LAM;
      FunctionAnalysisManager FAM;
      CGSCCAnalysisManager CGAM;
      ModuleAnalysisManager MAM;

      PassBuilder PB;

      PB.registerModuleAnalyses(MAM);
      PB.registerCGSCCAnalyses(CGAM);
      PB.registerFunctionAnalyses(FAM);
      PB.registerLoopAnalyses(LAM);
      PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

      int instCount = TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug();

      InstCombinePass().run(*(TheModule->getFunction("SMT")), FAM);
      if (TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug() != instCount)
      {
        instCount = TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug();
        usedInstCombine = true;
      }
      AggressiveInstCombinePass().run(*(TheModule->getFunction("SMT")), FAM);
      if (TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug() != instCount)
      {
        instCount = TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug();
        usedAInstCombine = true;
      }
      ReassociatePass().run(*(TheModule->getFunction("SMT")), FAM);
      if (TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug() != instCount)
      {
        instCount = TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug();
        usedReassociate = true;
      }
      SCCPPass().run(*(TheModule->getFunction("SMT")), FAM);
      if (TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug() != instCount)
      {
        instCount = TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug();
        usedSCCP = true;
      }
      DCEPass().run(*(TheModule->getFunction("SMT")), FAM);
      if (TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug() != instCount)
      {
        instCount = TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug();
        usedDCE = true;
      }
      ADCEPass().run(*(TheModule->getFunction("SMT")), FAM);
      if (TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug() != instCount)
      {
        instCount = TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug();
        usedADCE = true;
      }
      InstSimplifyPass().run(*(TheModule->getFunction("SMT")), FAM);
      if (TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug() != instCount)
      {
        instCount = TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug();
        usedInstSimplify = true;
      }
      GVNPass().run(*(TheModule->getFunction("SMT")), FAM);
      if (TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug() != instCount)
      {
        instCount = TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug();
        usedGVN = true;
      }
      InstCombinePass().run(*(TheModule->getFunction("SMT")), FAM);
      if (TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug() != instCount)
      {
        instCount = TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug();
        usedInstCombine = true;
      }
      AggressiveInstCombinePass().run(*(TheModule->getFunction("SMT")), FAM);
      if (TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug() != instCount)
      {
        instCount = TheModule->getFunction("SMT")->getEntryBlock().sizeWithoutDebug();
        usedAInstCombine = true;
      }

    }

    
    context c;
    solver s(c);

    BuildSMT(&c, &s, TheModule->getFunction("SMT"));

    char * outputFilename;

    if(HasFlag(argc, argv, "-o") && (outputFilename = GetFlag(argc, argv, "-o")))
    {
      std::ofstream out(outputFilename);
      out << s.to_smt2();
      //raw_fd_ostream file(outputFilename, *(new std::error_code()));
      //TheModule->print(file, nullptr);
    }
    else
    {
      std::cout << s.to_smt2();
    }

    char * statFilename;
    //Print used pass information
    if (HasFlag(argc, argv, "-t") && (statFilename = GetFlag(argc, argv, "-t")))
    {
      std::ofstream out(statFilename, std::ios_base::app);
      out << inputFilename << ",true," << usedInstCombine  << "," << usedAInstCombine <<"," <<usedReassociate << "," << usedSCCP << ","<<usedDCE << "," << usedADCE << "," << usedInstSimplify << "," << usedGVN << "\n";
    }
  }
  catch(int i)
  {
    char * outputFilename;
    if(HasFlag(argc, argv, "-o") && (outputFilename = GetFlag(argc, argv, "-o")))
    {
      std::ofstream out(outputFilename);
      out << smt_str;
      //raw_fd_ostream file(outputFilename, *(new std::error_code()));
      //TheModule->print(file, nullptr);
    }
    else
    {
      std::cout << smt_str;
    }
    char * statFilename;
    if (HasFlag(argc, argv, "-t") && (statFilename = GetFlag(argc, argv, "-t")))
    {
      std::ofstream out(statFilename, std::ios_base::app);
      out << inputFilename << ",false";
    }  
  }



  return 0;
}
