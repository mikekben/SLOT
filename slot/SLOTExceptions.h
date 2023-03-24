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

    class UnsupportedSMTTypeException : public std::exception {
    std::string description;
    std::string expression;
    std::string string;

    public:
        UnsupportedSMTTypeException(std::string t_description, expr t_expression) : UnsupportedSMTTypeException(t_description,t_expression.to_string()) {}
        UnsupportedSMTTypeException(std::string t_description, std::string t_expression) : description(t_description), expression(t_expression)
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