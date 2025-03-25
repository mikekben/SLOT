#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallString.h"
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
#include <map>

#include"z3++.h"

#ifndef SMTMAPPING
#define SMTMAPPING std::map<std::string, expr>
#endif

using namespace llvm;
using namespace z3;

namespace SLOT
{
  class LLVMNode;
  class LLVMFunction;

  class LLVMFunction
  {
    public:
      static int varCounter;

      context &scx;
      SMTMAPPING variables;
      Function *contents;
      bool shiftToMultiply;
      expr extraVariables; // Hold results of bitcast to bitvector

      expr AddBCVariable(std::unique_ptr<LLVMNode> contents);

      LLVMFunction(bool t_shiftToMultiply, context &t_scx, Function *t_contents);
      expr ToSMT();

      // bool CheckAssignment(model m);
  };

  class LLVMNode
  {
    public:
      context& scx;
      //const SMTMAPPING& variables;
      Value *contents;
      bool shiftToMultiply;
      LLVMFunction& function;

      z3::sort SMTSort();
      unsigned Width();

      static std::unique_ptr<LLVMNode> MakeLLVMNode(bool shiftToMultiply, context& scx, LLVMFunction& function, Value *contents);

      LLVMNode(bool t_shiftToMultiply, context& t_scx, LLVMFunction& t_function, Value* t_contents);
      virtual ~LLVMNode() {}
      virtual expr ToSMT() = 0;
  };

  class LLVMArgument : public LLVMNode
  {
    public:
      expr ToSMT() override;
      LLVMArgument(bool t_shiftToMultiply, context& t_scx, LLVMFunction& function, Value* t_contents);
  };

  class LLVMConstant : public LLVMNode
  {
    public:
      expr ToSMT() override;
      LLVMConstant(bool t_shiftToMultiply, context& t_scx, LLVMFunction& function, Value* t_contents);
  };



  class LLVMExpression : public LLVMNode
  {
    public:
      inline Instruction* AsInstruction() { return (Instruction *)contents; }
      inline std::unique_ptr<LLVMNode> Child(unsigned n) { return LLVMNode::MakeLLVMNode(shiftToMultiply, scx, function, AsInstruction()->getOperand(n)); }
      inline unsigned Opcode() { return AsInstruction()->getOpcode(); }
      inline expr Zero() { return scx.bv_val(0,Width()); }

      expr ToSMT() override;
      LLVMExpression(bool t_shiftToMultiply, context& t_scx, LLVMFunction& function, Value* t_contents);
  };

  class LLVMIcmp : public LLVMExpression
  {
    public:

      inline CmpInst::Predicate Predicate() { return ((ICmpInst*)contents)->getPredicate(); }

      expr ToSMT() override;
      LLVMIcmp(bool t_shiftToMultiply, context& t_scx, LLVMFunction& function, Value* t_contents);
  };

  class LLVMFcmp : public LLVMExpression
  {
    public:

      inline CmpInst::Predicate Predicate() { return ((FCmpInst*)contents)->getPredicate(); }

      expr ToSMT() override;
      LLVMFcmp(bool t_shiftToMultiply, context& t_scx, LLVMFunction& function, Value* t_contents);
  };

  class LLVMIntrinsicCall : public LLVMExpression
  {
    public:
      static expr FPClassCheck(context& scx, expr val, int64_t bits);

      expr AsRoundingMode(unsigned n);

      expr ToSMT() override;
      LLVMIntrinsicCall(bool t_shiftToMultiply, context& t_scx, LLVMFunction& function, Value* t_contents);
  };

  

}
