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

#ifndef SMTMAPPING
#define SMTMAPPING std::map<std::string, expr>
#endif

using namespace llvm;
using namespace z3;

namespace SLOT
{
  class LLVMNode
  {
    public:
      context& scx;
      const SMTMAPPING& variables;
      Value *contents;
      bool shiftToMultiply;

      z3::sort SMTSort();
      unsigned Width();

      static std::unique_ptr<LLVMNode> MakeLLVMNode(bool shiftToMultiply, context& scx, const SMTMAPPING &variables, Value *contents);

      LLVMNode(bool t_shiftToMultiply, context& t_scx, const SMTMAPPING& t_variables, Value* t_contents);
      virtual ~LLVMNode() {}
      virtual expr ToSMT() = 0;
  };

  class LLVMArgument : public LLVMNode
  {
    public:
      expr ToSMT() override;
      LLVMArgument(bool t_shiftToMultiply, context& t_scx, const SMTMAPPING& t_variables, Value* t_contents);
  };

  class LLVMConstant : public LLVMNode
  {
    public:
      expr ToSMT() override;
      LLVMConstant(bool t_shiftToMultiply, context& t_scx, const SMTMAPPING& t_variables, Value* t_contents);
  };



  class LLVMExpression : public LLVMNode
  {
    public:
      inline Instruction* AsInstruction() { return (Instruction *)contents; }
      inline std::unique_ptr<LLVMNode> Child(unsigned n) { return LLVMNode::MakeLLVMNode(shiftToMultiply, scx, variables, AsInstruction()->getOperand(n)); }
      inline unsigned Opcode() { return AsInstruction()->getOpcode(); }
      inline expr Zero() { return scx.bv_val(0,Width()); }

      expr ToSMT() override;
      LLVMExpression(bool t_shiftToMultiply, context& t_scx, const SMTMAPPING& t_variables, Value* t_contents);
  };

  class LLVMIcmp : public LLVMExpression
  {
    public:

      inline CmpInst::Predicate Predicate() { return ((ICmpInst*)contents)->getPredicate(); }

      expr ToSMT() override;
      LLVMIcmp(bool t_shiftToMultiply, context& t_scx, const SMTMAPPING& t_variables, Value* t_contents);
  };

  class LLVMFcmp : public LLVMExpression
  {
    public:

      inline CmpInst::Predicate Predicate() { return ((FCmpInst*)contents)->getPredicate(); }

      expr ToSMT() override;
      LLVMFcmp(bool t_shiftToMultiply, context& t_scx, const SMTMAPPING& t_variables, Value* t_contents);
  };

  class LLVMIntrinsicCall : public LLVMExpression
  {
    public:
      static expr FPClassCheck(context& scx, expr val, int64_t bits);

      expr ToSMT() override;
      LLVMIntrinsicCall(bool t_shiftToMultiply, context& t_scx, const SMTMAPPING& t_variables, Value* t_contents);
  };

  

}
