/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Copyright (c) 2011  Ondra Lengal <ilengal@fit.vutbr.cz>
 *
 *  Description:
 *    The source code for the parser of Timbuk format.
 *
 *****************************************************************************/

// C++ headers
#include <regex>
#include <fstream>
#include <numeric>
#include <filesystem>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wold-style-cast"
#include <boost/algorithm/string/predicate.hpp>
#pragma GCC diagnostic pop

// AUTOQ headers
#include "autoq/error.hh"
#include "autoq/util/util.hh"
#include "autoq/util/string.hh"
#include "autoq/aut_description.hh"
#include "autoq/complex/complex.hh"
#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/symbol/predicate.hh"
#include "autoq/parsing/timbuk_parser.hh"
#include "autoq/parsing/timbuk_parser_util.hh"
#include "autoq/parsing/complex_parser.hh"
#include "autoq/complex/symbolic_complex.hh"
#include "autoq/parsing/symboliccomplex_parser.hh"
#include "autoq/parsing/constraint_parser.hh"

// ANTLR4 headers
#include "autoq/parsing/ExtendedDirac/EvaluationVisitor.h"

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
				// if (ops_parsed)
				// {
				// 	THROW_AUTOQ_ERROR("Ops already parsed!");
				// }

				// ops_parsed = true;

				// while (!str.empty())
				// {
				// 	std::string label = AUTOQ::String::read_word(str);
				// 	auto label_num = AUTOQ::String::parse_colonned_token(label);
                //     auto temp = symbol_converter<Symbol>(label_num.first);

				// 	// result.symbols[temp] = label_num.second;
				// }
			}
			else if ("States" == first_word)
			{
				if (states_parsed)
				{
					THROW_AUTOQ_ERROR("States already parsed!");
				}

				states_parsed = true;

				// while (!str.empty())
				// {
				// 	std::string state = AUTOQ::String::read_word(str);
				// 	auto state_num = AUTOQ::String::parse_colonned_token(state);
				// 	// result.states.insert(state_num.first);
                //     /****************************************************************************************/
                //     // assert(result.stateNum.FindFwd(state_num.first) == result.stateNum.end());
                //     result.stateNum++; //.insert(std::make_pair(state_num.first, result.stateNum.size()));
                //     /****************************************************************************************/
				// }
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

template <typename Symbol>
AUTOQ::Automata<Symbol> parse_automaton(const std::string& str, const std::map<std::string, Complex> &constants, const std::map<std::string, std::string> &predicates, bool &do_not_throw_term_undefined_error) {
    bool colored = false;
    bool start_transitions = false;
    bool already_root_states = false;
    AUTOQ::Automata<Symbol> result;
    std::map<std::string, typename AUTOQ::Automata<Symbol>::State> states;
    std::set<std::string> result_finalStates;

	std::vector<std::string> lines = AUTOQ::String::split_delim(str, '\n');
	for (const std::string& line : lines) {
		std::string str = AUTOQ::String::trim(line);
		if (str.empty()) { continue; }

		if (!start_transitions) {    // processing numbers
            if (str.substr(0, 7) == "Colored") {
                AUTOQ::String::read_word(str); // after this command, "str" is expected to be "Transitions"
                colored = true;
            }
            if (std::regex_search(str, std::regex("Root +States"))) { // processing root states
                while (!str.empty()) {
                    std::string state = AUTOQ::String::read_word(str);
                    auto state_num = AUTOQ::String::parse_colonned_token(state);
                    // result.finalStates.push_back(state_num.first);
                    /****************************************************************************/
                    // int t = atoi(state_num.first.c_str());
                    // if (t > result.stateNum) result.stateNum = t;
                    result_finalStates.insert(state_num.first); //result.stateNum.TranslateFwd(state_num.first));
                    /****************************************************************************/
                }
                already_root_states = true;
                continue;
            }
            if (str == "Transitions") {
                /*********************************************************************/
                /* IMPORTANT: Now we assume all transitions are colored transitions. */
                colored = true;
                /*********************************************************************/
                if (!already_root_states) {
                    THROW_AUTOQ_ERROR("Root states not specified.");
                }
                start_transitions = true;
                continue;
            }
        } else {	// processing transitions
			std::string invalid_trans_str = AUTOQ_LOG_PREFIX +
				"Invalid transition \"" + line + "\".";

			size_t arrow_pos = str.find("->");
			if (std::string::npos == arrow_pos) {
				THROW_AUTOQ_ERROR(invalid_trans_str);
			}

			std::string lhs = AUTOQ::String::trim(str.substr(0, arrow_pos));
			std::string rhs = AUTOQ::String::trim(str.substr(arrow_pos + 2));
			if (rhs.empty() || AUTOQ::String::contains_whitespace(rhs)) {
				THROW_AUTOQ_ERROR(invalid_trans_str);
			}

			size_t parens_begin_pos = lhs.find("(");
			size_t parens_end_pos = lhs.find(")");
            if (parens_begin_pos < lhs.find("]"))
                parens_begin_pos = std::string::npos;
            if (parens_end_pos < lhs.find("]"))
                parens_end_pos = std::string::npos;
			if (std::string::npos == parens_begin_pos) {	// no tuple of states -> leaf
				if ((std::string::npos != parens_end_pos) ||
					(!std::is_same_v<Symbol, AUTOQ::PredicateAutomata::Symbol> && AUTOQ::String::contains_whitespace(lhs)) ||
					lhs.empty()) {
					THROW_AUTOQ_ERROR(invalid_trans_str);
				}
                /*******************************************************************************************************************/
                assert(lhs.front() == '[' && lhs.back() == ']');
                lhs = lhs.substr(1, lhs.size()-2);
                int t;
                auto it = states.find(rhs);
                if (it == states.end()) {
                    t = states.size();
                    states[rhs] = t;
                } else
                    t = it->second; //atoi(rhs.c_str());
                if (t > result.stateNum) result.stateNum = t;
                if constexpr(std::is_same_v<Symbol, AUTOQ::TreeAutomata::Symbol>) {
                    try {
                        if (colored) {
                            std::istringstream ss(lhs); // Create a stringstream from the input string
                            std::string token; // Tokenize the input string using a comma delimiter
                            std::getline(ss, token, ',');
                            auto sym = Symbol(boost::lexical_cast<int>(token));
                            std::getline(ss, token, ',');
                            auto color = boost::lexical_cast<AUTOQ::TreeAutomata::Tag>(token);
                            result.transitions[AUTOQ::TreeAutomata::SymbolTag(sym, AUTOQ::TreeAutomata::Tag(color))][t].insert(std::vector<AUTOQ::TreeAutomata::State>());
                        } else {
                            result.transitions[AUTOQ::TreeAutomata::SymbolTag(Symbol(boost::lexical_cast<int>(lhs)), AUTOQ::TreeAutomata::Tag(1))][t].insert(std::vector<AUTOQ::TreeAutomata::State>());
                        }
                    } catch (...) {
                        if (colored) {
                            std::istringstream ss(lhs); // Create a stringstream from the input string
                            std::string token; // Tokenize the input string using a comma delimiter
                            std::getline(ss, token, ',');
                            auto it = constants.find(token);
                            if (it == constants.end()) {
                                if (do_not_throw_term_undefined_error) {
                                    do_not_throw_term_undefined_error = false;
                                    return {};
                                }
                                THROW_AUTOQ_ERROR("The constant \"" + token + "\" is not defined yet!");
                            }
                            auto sym = Symbol(it->second);
                            std::getline(ss, token, ',');
                            auto color = boost::lexical_cast<AUTOQ::TreeAutomata::Tag>(token);
                            result.transitions[AUTOQ::TreeAutomata::SymbolTag(sym, AUTOQ::TreeAutomata::Tag(color))][t].insert(std::vector<AUTOQ::TreeAutomata::State>());
                        } else {
                            auto it = constants.find(lhs);
                            if (it == constants.end()) {
                                if (do_not_throw_term_undefined_error) {
                                    do_not_throw_term_undefined_error = false;
                                    return {};
                                }
                                THROW_AUTOQ_ERROR("The constant \"" + lhs + "\" is not defined yet!");
                            }
                            result.transitions[AUTOQ::TreeAutomata::SymbolTag(Symbol(it->second), AUTOQ::TreeAutomata::Tag(1))][t].insert(std::vector<AUTOQ::TreeAutomata::State>());
                        }
                    }
                } else if constexpr(std::is_same_v<Symbol, AUTOQ::PredicateAutomata::Symbol>) {
                    try {
                        if (colored) {
                            std::istringstream ss(lhs); // Create a stringstream from the input string
                            std::string token; // Tokenize the input string using a comma delimiter
                            std::getline(ss, token, ',');
                            auto sym = Symbol(boost::lexical_cast<int>(token));
                            std::getline(ss, token, ',');
                            auto color = boost::lexical_cast<AUTOQ::PredicateAutomata::Tag>(token);
                            result.transitions[AUTOQ::PredicateAutomata::SymbolTag(sym, AUTOQ::PredicateAutomata::Tag(color))][t].insert(std::vector<AUTOQ::PredicateAutomata::State>());
                        } else {
                            result.transitions[AUTOQ::PredicateAutomata::SymbolTag(Symbol(boost::lexical_cast<int>(lhs)), AUTOQ::PredicateAutomata::Tag(1))][t].insert(std::vector<AUTOQ::TreeAutomata::State>());
                        }
                    } catch (...) {
                        if (colored) {
                            std::istringstream ss(lhs); // Create a stringstream from the input string
                            std::string token; // Tokenize the input string using a comma delimiter
                            std::getline(ss, token, ',');
                            auto it = predicates.find(token);
                            if (it == predicates.end()) {
                                if (do_not_throw_term_undefined_error) {
                                    do_not_throw_term_undefined_error = false;
                                    return {};
                                }
                                THROW_AUTOQ_ERROR("The constant \"" + token + "\" is not defined yet!");
                            }
                            auto sym = Symbol(it->second.c_str());
                            std::getline(ss, token, ',');
                            auto color = boost::lexical_cast<AUTOQ::PredicateAutomata::Tag>(token);
                            result.transitions[AUTOQ::PredicateAutomata::SymbolTag(sym, AUTOQ::PredicateAutomata::Tag(color))][t].insert(std::vector<AUTOQ::PredicateAutomata::State>());
                        } else {
                            auto it = predicates.find(lhs);
                            if (it == predicates.end()) {
                                if (do_not_throw_term_undefined_error) {
                                    do_not_throw_term_undefined_error = false;
                                    return {};
                                }
                                THROW_AUTOQ_ERROR("The predicate \"" + lhs + "\" is not defined yet!");
                            }
                            result.transitions[AUTOQ::PredicateAutomata::SymbolTag(Symbol(it->second.c_str()), AUTOQ::PredicateAutomata::Tag(1))][t].insert(std::vector<AUTOQ::TreeAutomata::State>());
                        }
                    }
                } else { // if constexpr(std::is_same_v<Symbol, AUTOQ::SymbolicAutomata::Symbol>) {
                    if (colored) {
                        std::istringstream ss(lhs); // Create a stringstream from the input string
                        std::string token; // Tokenize the input string using a comma delimiter
                        std::getline(ss, token, ',');
                        EvaluationVisitor<>::SymbolicComplexParser scp(token, constants);
                        auto sym = Symbol(scp.getSymbolicComplex());
                        std::getline(ss, token, ',');
                        auto color = boost::lexical_cast<AUTOQ::SymbolicAutomata::Tag>(token);
                        result.transitions[AUTOQ::SymbolicAutomata::SymbolTag(sym, AUTOQ::SymbolicAutomata::Tag(color))][t].insert(std::vector<AUTOQ::SymbolicAutomata::State>());
                        for (const auto &var: scp.getNewVars())
                            result.vars.insert(var);
                    } else {
                        EvaluationVisitor<>::SymbolicComplexParser scp(lhs, constants);
                        result.transitions[AUTOQ::SymbolicAutomata::SymbolTag(Symbol(scp.getSymbolicComplex()), AUTOQ::SymbolicAutomata::Tag(1))][t].insert(std::vector<AUTOQ::SymbolicAutomata::State>());
                        for (const auto &var: scp.getNewVars())
                            result.vars.insert(var);
                    }
                }
                /*******************************************************************************************************************/
			} else {	// contains a tuple of states -> internal
				if ((std::string::npos == parens_end_pos) ||
					(parens_begin_pos > parens_end_pos) ||
					(parens_end_pos != lhs.length() - 1)) {
					THROW_AUTOQ_ERROR(invalid_trans_str);
				}

				std::string symbol = AUTOQ::String::trim(lhs.substr(0, parens_begin_pos));
				if (symbol.empty()) {
					THROW_AUTOQ_ERROR(invalid_trans_str);
				}

                std::vector<typename AUTOQ::Automata<Symbol>::State> state_vector;
                std::string str_state_tuple = lhs.substr(parens_begin_pos + 1,
					parens_end_pos - parens_begin_pos - 1);
                std::vector<std::string> state_tuple = AUTOQ::String::split_delim(str_state_tuple, ',');
				for (std::string& state : state_tuple) {
					state = AUTOQ::String::trim(state);
					if (AUTOQ::String::contains_whitespace(state)) {
						THROW_AUTOQ_ERROR(invalid_trans_str);
					}

                    /*******************************************************************/
                    if (state.length() > 0) {
                        int t;
                        auto it = states.find(state);
                        if (it == states.end()) {
                            t = states.size();
                            states[state] = t;
                        } else
                            t = it->second; //atoi(state.c_str());
                        if (t > result.stateNum) result.stateNum = t;
                        state_vector.push_back(t);
                    }
                    /*******************************************************************/
				}

                /*********************************************************************************************/
                int t;
                auto it = states.find(rhs);
                if (it == states.end()) {
                    t = states.size();
                    states[rhs] = t;
                } else
                    t = it->second; //atoi(rhs.c_str());
                if (t > result.stateNum) result.stateNum = t;
                // if (symbol == "[1]")
                //     result.finalStates.push_back(t);
                symbol = symbol.substr(1, symbol.length()-2);
                if constexpr(std::is_same_v<Symbol, AUTOQ::TreeAutomata::Symbol>) {
                    if (colored) {
                        std::istringstream ss(symbol); // Create a stringstream from the input string
                        std::string token; // Tokenize the input string using a comma delimiter
                        std::getline(ss, token, ',');
                        auto sym = Symbol(boost::lexical_cast<int>(token));
                        std::getline(ss, token, ',');
                        auto color = boost::lexical_cast<AUTOQ::TreeAutomata::Tag>(token);
                        result.transitions[AUTOQ::TreeAutomata::SymbolTag(sym, AUTOQ::TreeAutomata::Tag(color))][t].insert(state_vector);
                    } else {
                        result.transitions[AUTOQ::TreeAutomata::SymbolTag(Symbol(boost::lexical_cast<int>(symbol)), AUTOQ::TreeAutomata::Tag(1))][t].insert(state_vector);
                    }
                    // if (boost::lexical_cast<int>(symbol) == 1)
                    //     result.finalStates.push_back(t);
                } else if constexpr(std::is_same_v<Symbol, AUTOQ::PredicateAutomata::Symbol>) {
                    if (colored) {
                        std::istringstream ss(symbol); // Create a stringstream from the input string
                        std::string token; // Tokenize the input string using a comma delimiter
                        std::getline(ss, token, ',');
                        auto sym = parse_symbol<Symbol>(token);
                        std::getline(ss, token, ',');
                        auto color = boost::lexical_cast<AUTOQ::PredicateAutomata::Tag>(token);
                        result.transitions[AUTOQ::PredicateAutomata::SymbolTag(sym, AUTOQ::PredicateAutomata::Tag(color))][t].insert(state_vector);
                        // if (boost::lexical_cast<int>(sym.qubit()) == 1)
                        //     result.finalStates.push_back(t);
                    } else {
                        result.transitions[AUTOQ::PredicateAutomata::SymbolTag(parse_symbol<Symbol>(symbol), AUTOQ::PredicateAutomata::Tag(1))][t].insert(state_vector);
                    }
                } else { // if constexpr(std::is_same_v<Symbol, AUTOQ::SymbolicAutomata::Symbol>) {
                    if (colored) {
                        std::istringstream ss(symbol); // Create a stringstream from the input string
                        std::string token; // Tokenize the input string using a comma delimiter
                        std::getline(ss, token, ',');
                        auto sym = parse_symbol<Symbol>(token);
                        std::getline(ss, token, ',');
                        auto color = boost::lexical_cast<AUTOQ::SymbolicAutomata::Tag>(token);
                        result.transitions[AUTOQ::SymbolicAutomata::SymbolTag(sym, AUTOQ::SymbolicAutomata::Tag(color))][t].insert(state_vector);
                        // if (boost::lexical_cast<int>(sym.qubit()) == 1)
                        //     result.finalStates.push_back(t);
                    } else {
                        auto temp = parse_symbol<Symbol>(symbol);
                        result.transitions[AUTOQ::SymbolicAutomata::SymbolTag(temp, AUTOQ::SymbolicAutomata::Tag(1))][t].insert(state_vector);
                        // if (boost::lexical_cast<int>(temp.qubit()) == 1)
                        //     result.finalStates.push_back(t);
                    }
                }
                /*********************************************************************************************/
			}
		}
	}

	if (!start_transitions) {
		THROW_AUTOQ_ERROR("Transitions not specified.");
	}

    for (const auto &kv : result.transitions) {
        if (kv.first.is_internal()) {
            if (kv.first.symbol().qubit() > INT_MAX)
                THROW_AUTOQ_ERROR("The number of qubits is too large!");
            result.qubitNum = std::max(result.qubitNum, static_cast<int>(kv.first.symbol().qubit()));
        }
    }

    for (const auto &s : result_finalStates) {
        auto it = states.find(s);
        if (it != states.end())
            result.finalStates.push_back(it->second);
    }
    result.stateNum++; // because the state number starts from 0
	return result;
}

template <typename Symbol, typename Symbol2>
AUTOQ::Automata<Symbol> AUTOQ::Parsing::TimbukParser<Symbol, Symbol2>::parse_extended_dirac_from_istream(std::istream *is, bool &do_not_throw_term_undefined_error, const std::map<std::string, AUTOQ::Complex::Complex> &constants, const std::string &predicateConstraints) {
    bool start_transitions = false;
    // bool get_ordering = false;
    AUTOQ::Automata<Symbol> aut_final;
    std::string line;
    //reordering
    std::vector<int> ordering_map;
    std::string extended_dirac;

    while (std::getline(*is, line))
    {
		line = AUTOQ::String::trim(line);
        // std::cout<<line<<std::endl;
		if (line.empty())
        {
            continue;
        }
        // if (line == "Variable Order")
        // {
        //     std::getline(*is, line);
        //     ordering_map = qubit_ordering(line);
        //     get_ordering = true;
        // }
		else if (!start_transitions)
        {
            if (std::regex_search(line, std::regex("Extended +Dirac")))
            {
                start_transitions = true;
                continue;
            } else {
                THROW_AUTOQ_ERROR("The section \"Extended Dirac\" should be declared first before specifying the states.");
            }
        }   // processing states
        else
        {
            // auto a = do_not_throw_term_undefined_error;
            // //to do : make line with reordering e.g. |ii000> -> |00000> || |11000> ... make two lines then reorder
            // if(get_ordering)
            // {
            //     std::vector<std::string> equation_expension = state_expansion(line, ordering_map);
            //     for(unsigned i = 0 ; i < equation_expension.size(); i++)
            //     {
            //         auto aut = from_line_to_automaton<Symbol>(equation_expension[i], constants, predicates, do_not_throw_term_undefined_error);
            //         if (a && !do_not_throw_term_undefined_error) {
            //             return {};
            //         }
            //         aut_final = aut_final.operator||(aut);
            //         aut_final.reduce();
            //     }
            // }
            // else
            // {
            //     auto aut = from_line_to_automaton<Symbol>(line, constants, predicates,do_not_throw_term_undefined_error);
            //     if (a && !do_not_throw_term_undefined_error) {
            //             return {};
            //     }
            //     aut_final = aut_final.operator||(aut);
            // }
            // aut_final.reduce();
            extended_dirac += line + '\n'; // Do NOT miss '\n' for the ANTLR to parse correctly with '\n'
        }
    }

    /****************************************
    * Parse the Extended Dirac with ANTLR v4.
    *****************************************/
    EvaluationVisitor<Symbol> visitor({constants}, {predicateConstraints});
    auto extended_dirac2 = std::any_cast<std::string>(visitor.let_visitor_parse_string(extended_dirac));
    visitor.mode = EvaluationVisitor<Symbol>::COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES;
    typename EvaluationVisitor<Symbol>::segment2split_t segment2split = std::any_cast<typename EvaluationVisitor<Symbol>::segment2split_t>(visitor.let_visitor_parse_string(extended_dirac2));
    visitor.mode = EvaluationVisitor<Symbol>::REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT;
    visitor.segment2split = segment2split;
    auto extended_dirac3 = std::any_cast<std::string>(visitor.let_visitor_parse_string(extended_dirac2));
    visitor.mode = EvaluationVisitor<Symbol>::COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION;
    auto segment2perm = std::any_cast<typename EvaluationVisitor<Symbol>::segment2perm_t>(visitor.let_visitor_parse_string(extended_dirac3));
    visitor.mode = EvaluationVisitor<Symbol>::REORDER_UNITS_BY_THE_GROUP;
    visitor.segment2perm = segment2perm;
    auto afterrewrite = std::any_cast<std::string>(visitor.let_visitor_parse_string(extended_dirac3));
    visitor.mode = EvaluationVisitor<Symbol>::EVALUATE_EACH_SET_BRACES_TO_LSTA;
    visitor.segment2perm = segment2perm;
    visitor.do_not_throw_term_undefined_error = do_not_throw_term_undefined_error;
    auto final = std::any_cast<std::vector<AUTOQ::Automata<Symbol>>>(visitor.let_visitor_parse_string(afterrewrite)).at(0);
    if (!visitor.do_not_throw_term_undefined_error || visitor.encountered_term_undefined_error) {
        do_not_throw_term_undefined_error = false;
    }
    return final; // Evaluate using the visitor
    /****************************************/

    // DO NOT fraction_simplification() here since the resulting automaton may be used as pre.spec
    // and in this case all k's must be the same.
    // return aut_final;
}
template <typename Symbol, typename Symbol2>
std::pair<std::vector<AUTOQ::Automata<Symbol>>, std::vector<int>>
AUTOQ::Parsing::TimbukParser<Symbol, Symbol2>::parse_n_extended_diracs_from_istream(std::vector<std::istream*> isVec,
                                                                              const std::vector<std::map<std::string, AUTOQ::Complex::Complex>> &constantsVec,
                                                                              const std::vector<std::string> &predicateConstraintsVec) {
    std::vector<std::string> extended_dirac(isVec.size()); //[2];
    std::vector<std::vector<std::string>> exprs(isVec.size()); //[4]; // A1 \ A2; B1 \ B2
    int i = 0;
    for (std::istream *is : isVec) {
        bool start_transitions = false;
        std::string line;
        while (std::getline(*is, line))
        {
            line = AUTOQ::String::trim(line);
            if (line.empty()) { continue; }
            else if (!start_transitions)
            {
                if (std::regex_search(line, std::regex("Extended +Dirac")))
                {
                    start_transitions = true;
                    continue;
                } else {
                    THROW_AUTOQ_ERROR("The section \"Extended Dirac\" should be declared first before specifying the states.");
                }
            } else { // processing states
                extended_dirac[i] += line + '\n'; // Do NOT miss '\n' for the ANTLR to parse correctly with '\n'
            }
        }
        EvaluationVisitor<Symbol, Symbol2> visitor({constantsVec[i]}, {predicateConstraintsVec[i]});
        visitor.mode = EvaluationVisitor<Symbol, Symbol2>::EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT;
        auto extended_dirac2 = std::any_cast<std::string>(visitor.let_visitor_parse_string(extended_dirac[i]));
        visitor.mode = EvaluationVisitor<Symbol, Symbol2>::SPLIT_TENSORED_EXPRESSION_INTO_VECTOR_OF_SETS_WITHOUT_TENSOR;
        exprs[i] = std::any_cast<std::vector<std::string>>(visitor.let_visitor_parse_string(extended_dirac2)); // now we assume it does NOT contain SETMINUS
        /**/
        i++;
    }
    // Notice that up to this point, exprs[0] and exprs[2] are mandatory, whereas exprs[1] and exprs[3] are optional.
    for (size_t i=1; i<exprs.size(); i++) {
        if (exprs[i-1].size() != exprs[i].size()) {
            AUTOQ::Util::Log::error("[ERROR] The 1st list of expressions: " + AUTOQ::Util::Convert::ToString(exprs[i-1]));
            AUTOQ::Util::Log::error("[ERROR] The 2nd list of expressions: " + AUTOQ::Util::Convert::ToString(exprs[i]));
            THROW_AUTOQ_ERROR("There are two *.hsl files not aligned!");
        }
    }

    std::vector<AUTOQ::Automata<Symbol>> results; // A1, resultA2;
    // AUTOQ::Automata<Symbol2> resultB1, resultB2;
    std::vector<int> qubit_permutation;
    for (size_t i=0; i<exprs[0].size(); ++i) {
        auto new_composited_expression = exprs[0][i]; // +
                                //         (exprs[1].empty() ? "" : (" ; " + exprs[1][i])) +
                                //  " ; " + exprs[2][i] +
                                //         (exprs[3].empty() ? "" : (" ; " + exprs[3][i]));
        for (size_t j=1; j<exprs.size(); j++) {
            // if (!exprs[j].empty()) {
                new_composited_expression += " ; " + exprs[j][i];
            // }
        }
        EvaluationVisitor<Symbol, Symbol2> visitor(constantsVec, predicateConstraintsVec); // any pair of constants and predicates can do
        visitor.mode = EvaluationVisitor<Symbol, Symbol2>::COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES;
        typename EvaluationVisitor<Symbol, Symbol2>::segment2split_t segment2split = std::any_cast<typename EvaluationVisitor<Symbol, Symbol2>::segment2split_t>(visitor.let_visitor_parse_string(new_composited_expression));
        visitor.mode = EvaluationVisitor<Symbol, Symbol2>::REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT;
        visitor.segment2split = segment2split;
        auto extended_diracC = std::any_cast<std::string>(visitor.let_visitor_parse_string(new_composited_expression));

        /*********************************************************************************/
        int counter = 0;
        std::vector<std::vector<int>> expand_to_qubits;
        for (int len : visitor.remember_the_lengths_of_each_unit_position) {
            std::vector<int> qubits(len);
            std::iota(qubits.begin(), qubits.end(), counter); // Fill with 0, 1, ..., len-1
            expand_to_qubits.push_back(qubits);
            counter += len;
        }
        /*********************************************************************************/

        visitor.mode = EvaluationVisitor<Symbol, Symbol2>::COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION;
        auto segment2perm = std::any_cast<typename EvaluationVisitor<Symbol, Symbol2>::segment2perm_t>(visitor.let_visitor_parse_string(extended_diracC));
        if (segment2perm.size() != 1) {
            THROW_AUTOQ_ERROR("We only process one tensor segment at a time.");
        }
        auto base = qubit_permutation.size();
        for (const auto &cc : *segment2perm.begin()) {
            for (size_t i=0; i<expand_to_qubits.at(*cc.begin()).size(); i++) {
                for (auto g : cc) {
                    qubit_permutation.push_back(base + expand_to_qubits.at(g).at(i));
                }
            }
        }

        // I think that from this point, we don't need to bind the two automata together.
        // We can process them separately.
        std::stringstream ss(extended_diracC);
        std::string item;
        int j = -1;
        while (std::getline(ss, item, ';')) {
            std::string trimmed = AUTOQ::String::trim(item);
            if (!trimmed.empty()) {
                j++;
                // if (exprs[j].empty()) j++; // skip the empty one
                // if (j == 0) {
                    EvaluationVisitor<Symbol> visitor({constantsVec[j]}, {predicateConstraintsVec[j]});
                    visitor.mode = EvaluationVisitor<Symbol>::REORDER_UNITS_BY_THE_GROUP;
                    visitor.segment2perm = segment2perm;
                    auto afterrewrite = std::any_cast<std::string>(visitor.let_visitor_parse_string(trimmed));
                    visitor.mode = EvaluationVisitor<Symbol>::EVALUATE_EACH_SET_BRACES_TO_LSTA;
                    visitor.segment2perm = segment2perm;
                    // visitor.constants2 = constants2;
                    // visitor.predicateConstraints2 = predicateConstraints2;
                    auto final = std::any_cast<std::vector<AUTOQ::Automata<Symbol>>>(visitor.let_visitor_parse_string(afterrewrite)).at(0);
                    if (i == 0) {
                        // resultA1 = final;
                        results.push_back(final);
                    } else {
                        // resultA1 = resultA1.operator*(final);
                        results.at(j) = results.at(j).operator*(final);
                    }
                // }
            } else {
                THROW_AUTOQ_ERROR("Impossible case!");
            }
        }
    }

    // DO NOT fraction_simplification() here since the resulting automaton may be used as pre.spec
    // and in this case all k's must be the same.
    size_t N = qubit_permutation.size();
    std::vector<int> inverse_permutation(N);
    for (size_t i = 0; i < N; ++i) {
        inverse_permutation[qubit_permutation[i]] = i;
    }
    // if (!exprs[1].empty()) resultA2.print_language("resultA2\n");
    return std::make_pair(results, inverse_permutation);
}

template <typename Symbol>
AUTOQ::Automata<Symbol> parse_extended_dirac(const std::string& str, const std::map<std::string, Complex> &constants, const std::string &predicateConstraints, bool &do_not_throw_term_undefined_error) {
    std::istringstream inputStream(str); // delimited by '\n'
    auto aut = AUTOQ::Parsing::TimbukParser<Symbol>::parse_extended_dirac_from_istream(&inputStream, do_not_throw_term_undefined_error, constants, predicateConstraints);
    // aut.print(str);
    return aut;
}
template <typename Symbol, typename Symbol2>
std::pair<std::vector<AUTOQ::Automata<Symbol>>, std::vector<int>> parse_n_extended_diracs(const std::vector<std::string>& strVec, const std::vector<std::map<std::string, Complex>> &constantsVec, const std::vector<std::string> &predicateConstraintsVec) {
    // Store the actual streams so they live until the function returns
    std::vector<std::istringstream> streamStorage;
    std::vector<std::istream*> istreamVec;

    streamStorage.reserve(strVec.size());
    istreamVec.reserve(strVec.size());

    // Create istringstreams from each string and store their addresses
    for (const auto& str : strVec) {
        streamStorage.emplace_back(str);
        istreamVec.push_back(&streamStorage.back());
    }
    return AUTOQ::Parsing::TimbukParser<Symbol, Symbol2>::parse_n_extended_diracs_from_istream(istreamVec, constantsVec, predicateConstraintsVec);
}

template <typename Symbol, typename Symbol2>
AUTOQ::Automata<Symbol> AUTOQ::Parsing::TimbukParser<Symbol, Symbol2>::ReadAutomaton(const std::string& filepath) {
    bool do_not_throw_term_undefined_error = false;
    return AUTOQ::Parsing::TimbukParser<Symbol, Symbol2>::ReadAutomaton(filepath, do_not_throw_term_undefined_error);
}
template <typename Symbol, typename Symbol2>
AUTOQ::Automata<Symbol> AUTOQ::Parsing::TimbukParser<Symbol, Symbol2>::ReadAutomaton(const std::string& filepath, bool &do_not_throw_term_undefined_error) {
try {
    AUTOQ::Automata<Symbol> result;
    std::string automaton, constraints;
    std::string fileContents = AUTOQ::Util::ReadFile(filepath);
    std::map<std::string, AUTOQ::Complex::Complex> constants;
    // std::map<std::string, std::string> predicates;

    std::string::size_type pos = 0;
    while ((pos = fileContents.find("//", pos)) != std::string::npos) {
        std::string::size_type end = fileContents.find('\n', pos);
        if (end == std::string::npos) {
            fileContents.erase(pos);
        } else {
            fileContents.erase(pos, end - pos + 1);
        }
    }

    if (!boost::algorithm::ends_with(filepath, ".aut") &&
        (fileContents.find("Constants") != std::string::npos/* ||
         fileContents.find("Predicates") != std::string::npos*/)) {
        size_t found2 = std::min({fileContents.find("Extended"), fileContents.find("Root"),fileContents.find("Variable")});
        if (found2 == std::string::npos) {
            THROW_AUTOQ_ERROR("Neither \"Extended Dirac\" nor \"Root States\" are specified.");
        }

        if (fileContents.find("Constants") != std::string::npos) {
            std::string constants_str = AUTOQ::String::trim(fileContents.substr(std::string("Constants").length(), found2 - std::string("Constants").length()));
            fileContents = fileContents.substr(found2);
            std::stringstream ss(constants_str);
            std::string str;
            while (std::getline(ss, str, '\n')) {
                size_t arrow_pos = str.find(":=");
                if (std::string::npos != arrow_pos) { // Variables may appear without values in the symbolic case.
                    std::string lhs = AUTOQ::String::trim(str.substr(0, arrow_pos));
                    std::string rhs = AUTOQ::String::trim(str.substr(arrow_pos + 2));
                    if (lhs.empty() || rhs.empty()) {
                        THROW_AUTOQ_ERROR("Invalid number \"" + str + "\".");
                    }
                    if (constants.find(lhs) == constants.end()) {
                        constants[lhs] = EvaluationVisitor<>::ComplexParser(rhs).getComplex();
                    } else {
                        THROW_AUTOQ_ERROR("The constant \"" + lhs + "\" is already defined.");
                    }
                }
            }
        }
        // if (fileContents.find("Predicates") != std::string::npos) {
        //     std::string predicates_str = AUTOQ::String::trim(fileContents.substr(std::string("Predicates").length(), found2 - std::string("Predicates").length()));
        //     fileContents = fileContents.substr(found2);
        //     std::stringstream ss(predicates_str);
        //     std::string str;
        //     while (std::getline(ss, str, '\n')) {
        //         size_t arrow_pos = str.find(":=");
        //         if (std::string::npos != arrow_pos) { // Variables may appear without values in the symbolic case.
        //             std::string lhs = AUTOQ::String::trim(str.substr(0, arrow_pos));
        //             std::string rhs = AUTOQ::String::trim(str.substr(arrow_pos + 2));
        //             if (lhs.empty() || rhs.empty()) {
        //                 THROW_AUTOQ_ERROR("Invalid number \"" + str + "\".");
        //             }
        //             if (predicates.find(lhs) == predicates.end()) {
        //                 predicates[lhs] = rhs;
        //             } else {
        //                 THROW_AUTOQ_ERROR("The predicate \"" + lhs + "\" is already defined.");
        //             }
        //         }
        //     }
        // }

        #ifdef COMPLEX_FiveTuple
        // Unify k's for all complex numbers if 5-tuple is used
        // for speeding up binary operations.
        boost::multiprecision::cpp_int max_k = INT_MIN;
        for (const auto &kv : constants) {
            if (kv.second.at(0)!=0 || kv.second.at(1)!=0 || kv.second.at(2)!=0 || kv.second.at(3)!=0)
                if (max_k < kv.second.at(4))
                    max_k = kv.second.at(4);
        }
        if (max_k == INT_MIN) max_k = 0; // IMPORTANT: if not modified, resume to 0.
        for (auto &kv : constants) {
            if (kv.second.at(0)==0 && kv.second.at(1)==0 && kv.second.at(2)==0 && kv.second.at(3)==0)
                kv.second.at(4) = max_k;
            else {
                kv.second.increase_to_k(max_k);
            }
        }
        #endif

        #ifdef COMPLEX_nTuple
        // Unify k's for all complex numbers if n-tuple is used
        // for speeding up binary operations.
        boost::multiprecision::cpp_int max_k = INT_MIN;
        for (const auto &kv : constants) {
            if (!kv.second.empty())
                if (max_k < kv.second.k())
                    max_k = kv.second.k();
        }
        if (max_k == INT_MIN) max_k = 0; // IMPORTANT: if not modified, resume to 0.
        for (auto &kv : constants) {
            if (kv.second.empty())
                kv.second.k() = max_k;
            else {
                kv.second.adjust_k(max_k - kv.second.k());
            }
        }
        #endif
    }

    size_t found = fileContents.find("Constraints");
    if (found != std::string::npos) {
        automaton = fileContents.substr(0, found);
        constraints = fileContents.substr(found + 11); // "Constraints".length()
    } else {
        automaton = fileContents;
        constraints = "";
    }
    if (boost::algorithm::ends_with(filepath, ".lsta")) {
        // For now, we nonpublicly support *.lsta as usual fixing the original qubit order.
        // THROW_AUTOQ_ERROR("The filename extension \".lsta\" is currently disabled. Please use \".hsl\" instead.");
        std::map<std::string, std::string> dummy_predicates;
        result = parse_automaton<Symbol>(automaton, constants, dummy_predicates, do_not_throw_term_undefined_error);
    } else if (boost::algorithm::ends_with(filepath, ".aut")) {
        result = parse_timbuk<Symbol>(automaton);
    } else if (boost::algorithm::ends_with(filepath, ".hsl")) {
        result = parse_extended_dirac<Symbol>(automaton, constants, constraints, do_not_throw_term_undefined_error);
        // result.print_aut(filepath + "\n");
    } else {
        THROW_AUTOQ_ERROR("The filename extension is not supported.");
    }

    if constexpr (std::is_same_v<Symbol, AUTOQ::Symbol::Symbolic>) {
        std::stringstream ss(AUTOQ::String::trim(constraints));
        std::string constraint;
        while (std::getline(ss, constraint, '\n')) {
            result.constraints += EvaluationVisitor<>::ConstraintParser(constraint, constants).getSMTexpression();
        }
        if (!result.constraints.empty())
            result.constraints = "(and " + result.constraints + ")";
        else
            result.constraints = "true";
        // for (const auto &var : result.vars) {
        //     result.constraints = "(declare-const " + var + " Real)" + result.constraints;
        // }
    }
    return result;
} catch (AutoQError &e) {
    AUTOQ::Util::Log::error(e.what());
    THROW_AUTOQ_ERROR("(while parsing the automaton: " + filepath + ")");
}
}

template <typename Symbol, typename Symbol2>
std::pair<std::vector<AUTOQ::Automata<Symbol>>, std::vector<int>> AUTOQ::Parsing::TimbukParser<Symbol, Symbol2>::ReadTwoAutomata(const std::string& filepath1, const std::string& filepath2, const std::string &circuitPath) {
try {
    std::vector<std::string> filepathVec = {filepath1, filepath2};
    if (!circuitPath.empty()) {
        auto filepathVec2 = AUTOQ::Parsing::find_all_loop_invariants(circuitPath.c_str());
        filepathVec.insert(filepathVec.end(), filepathVec2.begin(), filepathVec2.end());
    }
    std::vector<std::string> automatonVec(filepathVec.size());
    std::vector<std::string> fileContents(filepathVec.size());
    std::vector<std::string> constraints(filepathVec.size());
    std::vector<std::map<std::string, AUTOQ::Complex::Complex>> constants(filepathVec.size());
    // std::map<std::string, std::string> predicates[2];

    for (size_t i=0; i<filepathVec.size(); i++) { // there are two automata possibly along with loop invariants
        fileContents[i] = AUTOQ::Util::ReadFile(filepathVec[i]);
        std::string::size_type pos = 0;
        while ((pos = fileContents[i].find("//", pos)) != std::string::npos) {
            std::string::size_type end = fileContents[i].find('\n', pos);
            if (end == std::string::npos) {
                fileContents[i].erase(pos);
            } else {
                fileContents[i].erase(pos, end - pos + 1);
            }
        }
        if (!boost::algorithm::ends_with(filepathVec[i], ".aut") &&
            (fileContents[i].find("Constants") != std::string::npos ||
            fileContents[i].find("Predicates") != std::string::npos)) {
            size_t found = std::min({fileContents[i].find("Extended"), fileContents[i].find("Root"), fileContents[i].find("Variable")});
            if (found == std::string::npos) {
                THROW_AUTOQ_ERROR("Neither \"Extended Dirac\" nor \"Root States\" are specified.");
            }
            if (fileContents[i].find("Constants") != std::string::npos) {
                std::string constants_str = AUTOQ::String::trim(fileContents[i].substr(std::string("Constants").length(), found - std::string("Constants").length()));
                fileContents[i] = fileContents[i].substr(found);
                std::stringstream ss(constants_str);
                std::string str;
                while (std::getline(ss, str, '\n')) {
                    size_t arrow_pos = str.find(":=");
                    if (std::string::npos != arrow_pos) { // Variables may appear without values in the symbolic case.
                        std::string lhs = AUTOQ::String::trim(str.substr(0, arrow_pos));
                        std::string rhs = AUTOQ::String::trim(str.substr(arrow_pos + 2));
                        if (lhs.empty() || rhs.empty()) {
                            THROW_AUTOQ_ERROR("Invalid number \"" + str + "\".");
                        }
                        if (constants[i].find(lhs) == constants[i].end()) {
                            constants[i][lhs] = EvaluationVisitor<>::ComplexParser(rhs).getComplex();
                        } else {
                            THROW_AUTOQ_ERROR("The constant \"" + lhs + "\" is already defined.");
                        }
                    }
                }
            }
            // if (fileContents[i].find("Predicates") != std::string::npos) {
            //     std::string predicates_str = AUTOQ::String::trim(fileContents[i].substr(std::string("Predicates").length(), found - std::string("Predicates").length()));
            //     fileContents[i] = fileContents[i].substr(found);
            //     std::stringstream ss(predicates_str);
            //     std::string str;
            //     while (std::getline(ss, str, '\n')) {
            //         size_t arrow_pos = str.find(":=");
            //         if (std::string::npos != arrow_pos) { // Variables may appear without values in the symbolic case.
            //             std::string lhs = AUTOQ::String::trim(str.substr(0, arrow_pos));
            //             std::string rhs = AUTOQ::String::trim(str.substr(arrow_pos + 2));
            //             if (lhs.empty() || rhs.empty()) {
            //                 THROW_AUTOQ_ERROR("Invalid number \"" + str + "\".");
            //             }
            //             if (predicates[i].find(lhs) == predicates[i].end()) {
            //                 predicates[i][lhs] = rhs;
            //             } else {
            //                 THROW_AUTOQ_ERROR("The predicate \"" + lhs + "\" is already defined.");
            //             }
            //         }
            //     }
            // }

            #ifdef COMPLEX_FiveTuple
            // Unify k's for all complex numbers if 5-tuple is used
            // for speeding up binary operations.
            boost::multiprecision::cpp_int max_k = INT_MIN;
            for (const auto &kv : constants[i]) {
                if (kv.second.at(0)!=0 || kv.second.at(1)!=0 || kv.second.at(2)!=0 || kv.second.at(3)!=0)
                    if (max_k < kv.second.at(4))
                        max_k = kv.second.at(4);
            }
            if (max_k == INT_MIN) max_k = 0; // IMPORTANT: if not modified, resume to 0.
            for (auto &kv : constants[i]) {
                if (kv.second.at(0)==0 && kv.second.at(1)==0 && kv.second.at(2)==0 && kv.second.at(3)==0)
                    kv.second.at(4) = max_k;
                else {
                    kv.second.increase_to_k(max_k);
                }
            }
            #endif

            #ifdef COMPLEX_nTuple
            // Unify k's for all complex numbers if n-tuple is used
            // for speeding up binary operations.
            boost::multiprecision::cpp_int max_k = INT_MIN;
            for (const auto &kv : constants[i]) {
                if (!kv.second.empty())
                    if (max_k < kv.second.k())
                        max_k = kv.second.k();
            }
            if (max_k == INT_MIN) max_k = 0; // IMPORTANT: if not modified, resume to 0.
            for (auto &kv : constants[i]) {
                if (kv.second.empty())
                    kv.second.k() = max_k;
                else {
                    kv.second.adjust_k(max_k - kv.second.k());
                }
            }
            #endif
        }

        size_t found = fileContents[i].find("Constraints");
        if (found != std::string::npos) {
            automatonVec[i] = fileContents[i].substr(0, found);
            constraints[i] = fileContents[i].substr(found + 11); // "Constraints".length()
        } else {
            automatonVec[i] = fileContents[i];
            constraints[i] = "";
        }
    }

    std::vector<AUTOQ::Automata<Symbol>> autVec;
    // AUTOQ::Automata<Symbol2> aut1;
    std::vector<int> qp; // qubit permutation
    // std::optional<AUTOQ::Automata<Symbol2>> autMinus;
    if (boost::algorithm::ends_with(filepathVec[0], ".hsl") && boost::algorithm::ends_with(filepathVec[1], ".hsl")) {
        std::tie(autVec, qp/*, autMinus*/) = parse_n_extended_diracs<Symbol, Symbol2>(automatonVec, constants, constraints);
    } else if (boost::algorithm::ends_with(filepathVec[0], ".lsta") && boost::algorithm::ends_with(filepathVec[1], ".lsta")) {
        autVec.reserve(filepathVec.size());
        // Do not reorder qubits (leaving qp empty) when the input is in *.lsta format.
        for (size_t i = 0; i < filepathVec.size(); ++i) {
            std::map<std::string, std::string> dummy_predicates;
            bool dummy_do_not_throw = false;
            autVec.emplace_back(parse_automaton<Symbol>(automatonVec[i], constants[i], dummy_predicates, dummy_do_not_throw));
        }
    } else {
        THROW_AUTOQ_ERROR("The filename extension is not supported.");
    }

    // using AutomataPair = std::variant<AUTOQ::Automata<Symbol>*, AUTOQ::Automata<Symbol2>*>;
    // std::vector<AutomataPair> auts = {
    //     AutomataPair{std::in_place_index<0>, &aut0},
    //     AutomataPair{std::in_place_index<1>, &aut1}
    // };
    int index = 0;
    for (auto &aut : autVec) {
        // std::visit([&](auto &aut) {
            // auto &aut = *autPtr;
            std::stringstream ss(AUTOQ::String::trim(constraints[index]));
            std::string constraint;
            while (std::getline(ss, constraint, '\n')) {
                aut.constraints += EvaluationVisitor<>::ConstraintParser(constraint, constants[index]).getSMTexpression();
            }
            if (!(aut.constraints).empty())
                aut.constraints = "(and " + aut.constraints + ")";
            else
                aut.constraints = "true";
            // for (const auto &var : aut.vars) {
            //     aut.constraints = "(declare-const " + var + " Real)" + aut.constraints;
            // }
        // }, v);
        index++;
    }
    return std::make_pair(autVec, qp/*, autMinus*/);
} catch (AutoQError &e) {
    AUTOQ::Util::Log::error(e.what());
    THROW_AUTOQ_ERROR("(while parsing the automaton: " + filepath1 + " or " + filepath2 + ")");
}
}

std::variant<AUTOQ::Automata<AUTOQ::Symbol::Concrete>, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>, AUTOQ::Automata<AUTOQ::Symbol::Predicate>> ReadAutomaton(const std::string& filepath) {
    std::string fileContents = AUTOQ::Util::ReadFile(filepath);
    if (fileContents.find("Predicates") != std::string::npos) {
        return AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>::ReadAutomaton(filepath);
    } else {
        bool do_not_throw_term_undefined_error = true;
        auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(filepath, do_not_throw_term_undefined_error);
        if (do_not_throw_term_undefined_error)
            return aut;
        else
            return AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadAutomaton(filepath);
    }
}

std::variant<AUTOQ::Automata<AUTOQ::Symbol::Concrete>, AUTOQ::Automata<AUTOQ::Symbol::Predicate>> ReadPossiblyPredicateAutomaton(const std::string& filepath) {
    std::string fileContents = AUTOQ::Util::ReadFile(filepath);
    bool do_not_throw_term_undefined_error = true;
    auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(filepath, do_not_throw_term_undefined_error);
    if (do_not_throw_term_undefined_error)
        return aut;
    else
        return AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>::ReadAutomaton(filepath);
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>;
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>;
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic, AUTOQ::Symbol::Predicate>;
