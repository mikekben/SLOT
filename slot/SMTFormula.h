#include "SMTNode.h"

#ifndef LLMAPPING
#define LLMAPPING std::map<std::string, Value*>
#endif

namespace SLOT
{
    class SMTFormula
    {
        public:
            LLVMContext& lcx;
            Module* lmodule;
            IRBuilder<>& builder;

            Function* function;

            std::string string;
            std::string func_name;
            expr_vector contents;
            std::vector<BooleanNode> assertions;
            LLMAPPING variables;

            SMTFormula(LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, std::string t_string, std::string t_func_name);
            void ToLLVM();

            //bool CheckAssignment(model m);
    };
}