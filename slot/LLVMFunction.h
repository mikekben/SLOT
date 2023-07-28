#include "LLVMNode.h"

#ifndef SMTMAPPING
#define SMTMAPPING std::map<std::string, expr>
#endif

namespace SLOT
{
    class LLVMFunction
    {
        public:

            context& scx;
            SMTMAPPING variables;
            Function* contents;
            bool shiftToMultiply;


            LLVMFunction(bool t_shiftToMultiply, context& t_scx, Function* t_contents);
            expr ToSMT();

            //bool CheckAssignment(model m);
    };
}