#ifndef AUTOQ_PARSING_TIMBUK_PARSER_GRAMMAR_HH
#define AUTOQ_PARSING_TIMBUK_PARSER_GRAMMAR_HH
/*****************************************************************************
 *  Timbuk symbol grammar used by .lsta transitions.
 *  Main function: parse_symbol(str [, vars]).
 *****************************************************************************/

/**
 * @brief  Parse a string with Timbuk definition of an automaton
 */
template <typename Symbol>
typename AUTOQ::Automata<Symbol>::Symbol parse_symbol(const std::string& str, std::set<std::string> &vars) {
    /**************************** SymbolicAutomata ****************************/
    if constexpr(std::is_same_v<Symbol, AUTOQ::SymbolicAutomata::Symbol>) {
        std::string str2 = str.substr(str.front()=='[', str.length() - (str.front()=='[') - (str.back()==']'));
        try {
            return AUTOQ::SymbolicAutomata::Symbol(boost::lexical_cast<boost::multiprecision::cpp_int>(str2.c_str()));
        } catch (boost::bad_lexical_cast& e) {
            auto sp = EvaluationVisitor<>::SymbolicComplexParser(str2);
            for (const auto &v : sp.getNewVars())
                vars.insert(v);
            return AUTOQ::SymbolicAutomata::Symbol(sp.getSymbolicComplex());
        }
    }
    /**************************** PredicateAutomata ****************************/
    else if constexpr(std::is_same_v<Symbol, AUTOQ::PredicateAutomata::Symbol>) {
        std::string str2 = str.substr(str.front()=='[', str.length() - (str.front()=='[') - (str.back()==']'));
        try {
            return AUTOQ::Symbol::Predicate(boost::multiprecision::cpp_int(str2));
        } catch (...) {
            return AUTOQ::Symbol::Predicate(str2.c_str());
        }
    }
    /***************************************************************************/
    else {
        THROW_AUTOQ_ERROR("The type of Symbol is not supported!");
    }
}
template <typename Symbol>
typename AUTOQ::Automata<Symbol>::Symbol parse_symbol(const std::string& str) {
    std::set<std::string> vars;
    return parse_symbol<Symbol>(str, vars);
}


#endif
