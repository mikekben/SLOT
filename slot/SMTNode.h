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

#include <iostream>


#include"z3++.h"

using namespace llvm;
using namespace z3;

namespace SLOT
{
  class IntegerNode;
  class FloatingNode;
  class BitvectorNode;
  class BooleanNode;

  class SMTNode
  {
    public:
      context& scx;
      LLVMContext& lcx;
      Module* lmodule;
      IRBuilder<>& builder;
      unsigned integer_width;
      const std::map<std::string, Value *>& variables;
      expr contents;
      

      //Z3 ''constants'' can be either variables or constants
      inline bool IsVariable() { return contents.is_const() && variables.count(contents.to_string()); }
      inline bool IsConstant() { return contents.is_const() && !variables.count(contents.to_string()); }
      inline Z3_decl_kind Op() { return contents.decl().decl_kind(); }

      //Syntax sugar for extracting children
      inline IntegerNode IntegerChild(expr cont);
      inline IntegerNode IntegerChild(int index);
      inline FloatingNode FloatingChild(expr cont);
      inline FloatingNode FloatingChild(int index);
      inline BitvectorNode BitvectorChild(expr cont);
      inline BitvectorNode BitvectorChild(int index);
      inline BooleanNode BooleanChild(expr cont);
      inline BooleanNode BooleanChild(int index);

      SMTNode(context& t_scx, LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, unsigned t_integer_width, const std::map<std::string, Value*>& t_variables, expr t_contents);
      virtual ~SMTNode() {}
      virtual Value* ToLLVM() = 0;
  };


  //--------------------------------------------------------------------------------


  class IntegerNode : public SMTNode
  {
    public:
      inline unsigned Width() { return integer_width; } //For possible extension

      static bool IsComparison(expr expression);
      Value* ToLLVM() override;
      IntegerNode(context& t_scx, LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, unsigned t_integer_width, const std::map<std::string, Value*>& t_variables, expr t_contents);
  };



  //--------------------------------------------------------------------------------

  class FloatingNode : public SMTNode
  {
    public:

      static const std::map<Z3_decl_kind, int> class_flags;

      inline unsigned SBits() { return contents.get_sort().fpa_sbits(); }
      inline unsigned Width() { return contents.get_sort().fpa_sbits() + contents.get_sort().fpa_ebits(); }
      
      static void CheckRM(expr e);
      static bool IsRoundingMode(expr e);
      
      static Type* ToFloatingType(LLVMContext& lcx, std::string name, unsigned width);

      Value * LLVMClassCheck(Z3_decl_kind op);
      Value * LLVMEq(FloatingNode other);
      Value * LLVMNE(FloatingNode other);


      Value* ToLLVM() override;
      FloatingNode(context& t_scx, LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, unsigned t_integer_width, const std::map<std::string, Value*>& t_variables, expr t_contents);
  };

  //--------------------------------------------------------------------------------

  class BitvectorNode : public SMTNode
  {
    public:
      inline unsigned Width() { return contents.get_sort().bv_size(); }
      static bool IsSignedComparison(expr expression);
      static bool IsUnsignedComparison(expr expression);
      static bool IsComparison(expr expression);
      static Value * LlIsZero(Value * val);
      static Value * LlIsNegative(Value * val);
      static Value * LlIsPositive(Value * val);
      static Value * LlURem(Value * left, Value * right);

      Value* ToLLVM() override;
      BitvectorNode(context& t_scx, LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, unsigned t_integer_width, const std::map<std::string, Value*>& t_variables, expr t_contents);
  };

//--------------------------------------------------------------------------------

  class BooleanNode : public SMTNode
  {
    public:

      Value* ToLLVM() override;
      BooleanNode(context& t_scx, LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, unsigned t_integer_width, const std::map<std::string, Value*>& t_variables, expr t_contents);
  };
}
