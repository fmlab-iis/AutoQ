#ifndef AUTOQ_PARSING_TIMBUK_PARSER_GRAMMAR_HH
#define AUTOQ_PARSING_TIMBUK_PARSER_GRAMMAR_HH
/*****************************************************************************
 *  Timbuk grammar and classic .aut format.
 *  Main functions: parse_symbol(str [, vars]), parse_timbuk(str).
 *****************************************************************************/

/**
 * @brief  Parse a string with Timbuk definition of an automaton
 */
template <typename Symbol>
typename AUTOQ::Automata<Symbol>::Symbol parse_symbol(const std::string& str, std::set<std::string> &vars) {
    /************************** TreeAutomata **************************/
    if constexpr(std::is_same_v<Symbol, AUTOQ::TreeAutomata::Symbol>) {
            THROW_AUTOQ_ERROR("The type of Complex is not supported!");
    }
    /**************************** SymbolicAutomata ****************************/
    else if constexpr(std::is_same_v<Symbol, AUTOQ::SymbolicAutomata::Symbol>) {
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

template <typename Symbol>
AUTOQ::Automata<Symbol> parse_timbuk(const std::string& str) {
	AUTOQ::Automata<Symbol> result;

	bool are_transitions = false;
	bool aut_parsed = false;
	// bool ops_parsed = false;
	bool states_parsed = false;
	bool final_parsed = false;

	std::vector<std::string> lines = AUTOQ::String::split_delim(str, '\n');
	for (const std::string& line : lines)
	{
		std::string str = AUTOQ::String::trim(line);
		if (str.empty()) { continue; }

		if (!are_transitions)
		{
			std::string first_word = AUTOQ::String::read_word(str);
			if ("Transitions" == first_word)
			{
				are_transitions = true;
				continue;
			}
			else if ("Automaton" == first_word)
			{
				if (aut_parsed)
				{
					THROW_AUTOQ_ERROR("Automaton already parsed!");
				}

				aut_parsed = true;

				result.name = AUTOQ::String::read_word(str);

				if (!str.empty())
				{
					THROW_AUTOQ_ERROR("Line \"" + line +
						"\" has an unexpected string.");
				}
			}
			else if ("Ops" == first_word)
			{
			}
			else if ("States" == first_word)
			{
				if (states_parsed)
				{
					THROW_AUTOQ_ERROR("States already parsed!");
				}

				states_parsed = true;
			}
			else if ("Final" == first_word)
			{
				std::string str_states = AUTOQ::String::read_word(str);
				if ("States" != str_states)
				{
					THROW_AUTOQ_ERROR("Line \"" + line +
						"\" contains an unexpected string.");
				}

				if (final_parsed)
				{
					THROW_AUTOQ_ERROR("Final States already parsed!");
				}

				final_parsed = true;

				while (!str.empty())
				{
					std::string state = AUTOQ::String::read_word(str);
					auto state_num = AUTOQ::String::parse_colonned_token(state);
					// result.finalStates.push_back(state_num.first);
                    /****************************************************************************/
                    int t = atoi(state_num.first.c_str());
                    if (t > result.stateNum) result.stateNum = t;
                    result.finalStates.push_back(t); //result.stateNum.TranslateFwd(state_num.first));
                    /****************************************************************************/
				}
			}
			else
			{	// guard
				THROW_AUTOQ_ERROR("Line \"" + line +
					"\" contains an unexpected string.");
			}
		}
		else
		{	// processing transitions
			std::string invalid_trans_str = AUTOQ_LOG_PREFIX +
				"Invalid transition \"" + line + "\".";

			size_t arrow_pos = str.find("->");
			if (std::string::npos == arrow_pos)
			{
				THROW_AUTOQ_ERROR(invalid_trans_str);
			}

			std::string lhs = AUTOQ::String::trim(str.substr(0, arrow_pos));
			std::string rhs = AUTOQ::String::trim(str.substr(arrow_pos + 2));

			if (rhs.empty() ||
				AUTOQ::String::contains_whitespace(rhs))
			{
				THROW_AUTOQ_ERROR(invalid_trans_str);
			}

			size_t parens_begin_pos = lhs.find("(");
			size_t parens_end_pos = lhs.find(")");
            if (parens_begin_pos < lhs.find("]"))
                parens_begin_pos = std::string::npos;
            if (parens_end_pos < lhs.find("]"))
                parens_end_pos = std::string::npos;
			if (std::string::npos == parens_begin_pos)
			{	// no tuple of states
				if ((std::string::npos != parens_end_pos) ||
					(!std::is_same_v<Symbol, AUTOQ::PredicateAutomata::Symbol> && AUTOQ::String::contains_whitespace(lhs)) ||
					lhs.empty())
				{
					THROW_AUTOQ_ERROR(invalid_trans_str);
				}

				// result.transitions.insert(AUTOQ::TreeAutomata::Transition({}, lhs, rhs));
                /*******************************************************************************************************************/
                int t = atoi(rhs.c_str());
                if (t > result.stateNum) result.stateNum = t;
                if constexpr(std::is_same_v<Symbol, AUTOQ::TreeAutomata::Symbol>) {
                    auto temp = parse_symbol<Symbol>(lhs);
                    result.transitions[temp][t].insert(std::vector<AUTOQ::TreeAutomata::State>()); //.stateNum.TranslateFwd(rhs));
                } else if constexpr(std::is_same_v<Symbol, AUTOQ::PredicateAutomata::Symbol>) {
                    auto temp = parse_symbol<Symbol>(lhs);
                    result.transitions[temp][t].insert(std::vector<AUTOQ::TreeAutomata::State>()); //.stateNum.TranslateFwd(rhs));
                } else {
                    auto temp = parse_symbol<Symbol>(lhs, result.vars);
                    result.transitions[temp][t].insert(std::vector<AUTOQ::SymbolicAutomata::State>()); //.stateNum.TranslateFwd(rhs));
                }
                /*******************************************************************************************************************/
			}
			else
			{	// contains a tuple of states
				if ((std::string::npos == parens_end_pos) ||
					(parens_begin_pos > parens_end_pos) ||
					(parens_end_pos != lhs.length() - 1))
				{
					THROW_AUTOQ_ERROR(invalid_trans_str);
				}

				std::string lab = AUTOQ::String::trim(lhs.substr(0, parens_begin_pos));

				if (lab.empty())
				{
					THROW_AUTOQ_ERROR(invalid_trans_str);
				}

				std::string str_state_tuple = lhs.substr(parens_begin_pos + 1,
					parens_end_pos - parens_begin_pos - 1);

				/********************************************/
                std::vector<typename AUTOQ::Automata<Symbol>::State> state_vector;
                /********************************************/
                std::vector<std::string> state_tuple = AUTOQ::String::split_delim(str_state_tuple, ',');
				for (std::string& state : state_tuple)
				{
					state = AUTOQ::String::trim(state);

					if (AUTOQ::String::contains_whitespace(state))
					{
						THROW_AUTOQ_ERROR(invalid_trans_str);
					}

                    /*******************************************************************/
                    if (state.length() > 0) {
                        int t = atoi(state.c_str());
                        if (t > result.stateNum) result.stateNum = t;
                        state_vector.push_back(t); //.stateNum.TranslateFwd(state));
                    }
                    /*******************************************************************/
				}

				if ((state_tuple.size() == 1) && state_tuple[0] == "")
				{
					state_tuple = { };
				}

				// result.transitions.insert(AUTOQ::TreeAutomata::Transition(state_tuple, lab, rhs));
                /*********************************************************************************************/
                int t = atoi(rhs.c_str());
                if (t > result.stateNum) result.stateNum = t;
                Symbol temp = parse_symbol<Symbol>(lab);
                result.transitions[temp][t].insert(state_vector);
                /*********************************************************************************************/
			}
		}
	}

	if (!are_transitions)
	{
		THROW_AUTOQ_ERROR("Transitions not specified.");
	}

    for (const auto &kv : result.transitions) {
        if (kv.first.is_internal()) {
            if (kv.first.symbol().qubit() > INT_MAX)
                THROW_AUTOQ_ERROR("The number of qubits is too large!");
            result.qubitNum = std::max(result.qubitNum, static_cast<int>(kv.first.symbol().qubit()));
        }
    }
    result.stateNum++;
	return result;
}


#endif
