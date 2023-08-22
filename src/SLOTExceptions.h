namespace SLOT
{
    class UnsupportedSMTOpException : public std::exception {
    std::string description;
    std::string expression;
    std::string string;

    public:
        UnsupportedSMTOpException(std::string t_description, expr t_expression) : description(t_description), expression(t_expression.to_string())
        {
            string = "Encountered unsupported SMT operation (" + description + ") in expression " + expression;
        }
        const char * what () const throw () 
        {
            return string.c_str();
        }
    };


    class UnsupportedLLVMOpException : public std::exception {
        Value* expression;
        std::string description;
        std::string string;

    public:
        UnsupportedLLVMOpException(std::string t_description, Value* t_expression) : description(t_description), expression(t_expression)
        {
            std::string mst;
            llvm::raw_string_ostream rso(mst);
            expression->print(rso);
            //throw UnsupportedTypeException("unsupported LLVM type", rso.str());
            string = "Encountered unsupported LLVM operation (" + description + ")" + rso.str();
        }
        const char * what () const throw () 
        {
            return string.c_str();
        }
    };


    class UnsupportedTypeException : public std::exception {
    std::string description;
    std::string expression;
    std::string string;

    public:
        UnsupportedTypeException(std::string t_description, expr t_expression) : UnsupportedTypeException(t_description,t_expression.to_string()) {}
        UnsupportedTypeException(std::string t_description, std::string t_expression) : description(t_description), expression(t_expression)
        {
            string = "Encountered unsupported SMT type (" + description + ") in expression " + expression;
        }
        const char * what () const throw () 
        {
            return string.c_str();
        }
    };

    class NotImplementedException : public std::logic_error
    {
        public:
            NotImplementedException() : std::logic_error("Function not yet implemented") { };
    };

    
}