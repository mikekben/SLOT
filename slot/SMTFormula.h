#include "SMTNode.h"

namespace SLOT
{
    class SMTFormula
    {
        public:
            context& scx;
            LLVMContext& lcx;
            Module* lmodule;
            IRBuilder<>& builder;

            Function* function;

            std::string string;
            expr_vector contents;
            std::vector<BooleanNode> assertions;
            unsigned integer_width;
            std::map<std::string, Value *> variables;

            SMTFormula(context& t_scx, LLVMContext& t_lcx, Module* t_lmodule, IRBuilder<>& t_builder, std::string t_string);
            void ToLLVM();
    };
}