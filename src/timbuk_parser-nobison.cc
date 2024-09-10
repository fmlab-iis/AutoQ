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
#include <boost/regex.hpp>
#include <boost/algorithm/string/predicate.hpp>

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
#include "autoq/parsing/complex_parser.hh"
#include "autoq/complex/symbolic_complex.hh"
#include "autoq/parsing/symboliccomplex_parser.hh"
#include "autoq/parsing/constraint_parser.hh"

template <typename Symbol>
AUTOQ::Automata<Symbol> from_tree_to_automaton(std::string tree, const std::map<std::string, AUTOQ::Complex::Complex> &constants, const std::map<std::string, std::string> &predicates, bool &do_not_throw_term_undefined_error) {
    /************************** TreeAutomata **************************/
    if constexpr(std::is_same_v<Symbol, AUTOQ::TreeAutomata::Symbol>) {
        AUTOQ::Automata<AUTOQ::Symbol::Concrete> aut;
        std::map<typename AUTOQ::Automata<AUTOQ::Symbol::Concrete>::State, AUTOQ::Symbol::Concrete> states_probs;
        AUTOQ::Complex::Complex default_prob(0);
        const std::regex myregex("(.*?)\\|(.*?)>");
        const std::regex_iterator<std::string::iterator> END;
        std::regex_iterator<std::string::iterator> it2(tree.begin(), tree.end(), myregex);
        while (it2 != END) { // c1|10> + c2|11> + c0|*>
            std::string state = it2->str(2); // 10
            std::string t = it2->str(1); // c1
            std::erase(t, ' ');
            if (!t.empty() && t.at(0) == '+') t = t.substr(1);
            if (t.empty()) t = "1";
            else if (t == "-") t = "-1";
            if (states_probs.empty()) {
                if (state == "*")
                    THROW_AUTOQ_ERROR("The numbers of qubits are not specified!");
                aut.qubitNum = state.length();
            } else if (state != "*" && ((aut.qubitNum < 0) || (static_cast<std::size_t>(aut.qubitNum) != state.length()))) {
                THROW_AUTOQ_ERROR("The numbers of qubits are not the same in all basis states!");
            }
            if (state == "*") {
                auto cp = ComplexParser(t, constants);
                if (!cp.getConstName().empty()) { // is symbol
                    auto it = constants.find(t);
                    if (it == constants.end()) {
                        if (do_not_throw_term_undefined_error) {
                            do_not_throw_term_undefined_error = false;
                            return {};
                        }
                        THROW_AUTOQ_ERROR("The constant \"" + t + "\" is not defined yet!");
                    }
                    default_prob += it->second;
                } else
                    default_prob += cp.getComplex();

            } else {
                AUTOQ::TreeAutomata::State s = std::stoll(state, nullptr, 2);
                auto cp = ComplexParser(t, constants);
                if (!cp.getConstName().empty()) { // is symbol
                    auto it = constants.find(t);
                    if (it == constants.end()) {
                        if (do_not_throw_term_undefined_error) {
                            do_not_throw_term_undefined_error = false;
                            return {};
                        }
                        THROW_AUTOQ_ERROR("The constant \"" + t + "\" is not defined yet!");
                    }
                    states_probs[s].complex += it->second;
                } else
                    states_probs[s].complex += cp.getComplex();
            }
            ++it2;
        }
        typename AUTOQ::Automata<AUTOQ::Symbol::Concrete>::State pow_of_two = 1;
        typename AUTOQ::Automata<AUTOQ::Symbol::Concrete>::State state_counter = 0;
        for (int level=1; level<=aut.qubitNum; level++) {
            for (typename AUTOQ::Automata<AUTOQ::Symbol::Concrete>::State i=0; i<pow_of_two; i++) {
                aut.transitions[typename AUTOQ::Automata<Symbol>::SymbolTag(AUTOQ::Symbol::Concrete(level), typename AUTOQ::Automata<Symbol>::Tag(1))][state_counter].insert({(state_counter<<1)+1, (state_counter<<1)+2});
                state_counter++;
            }
            pow_of_two <<= 1;
        }
        for (typename AUTOQ::Automata<AUTOQ::Symbol::Concrete>::State i=state_counter; i<=(state_counter<<1); i++) {
            auto spf = states_probs.find(i-state_counter);
            if (spf == states_probs.end()) {
                // if (default_prob == AUTOQ::Complex::Complex())
                //     THROW_AUTOQ_ERROR("The default amplitude is not specified!");
                aut.transitions[typename AUTOQ::Automata<Symbol>::SymbolTag(AUTOQ::Symbol::Concrete(default_prob), typename AUTOQ::Automata<Symbol>::Tag(1))][i].insert({{}});
            }
            else
                aut.transitions[typename AUTOQ::Automata<Symbol>::SymbolTag(spf->second, typename AUTOQ::Automata<Symbol>::Tag(1))][i].insert({{}});
        }
        aut.finalStates.push_back(0);
        aut.stateNum = (state_counter<<1) + 1;
        aut.reduce();
        return aut;
    } /**************************** SymbolicAutomata ****************************/
    else if constexpr(std::is_same_v<Symbol, AUTOQ::SymbolicAutomata::Symbol>) {
        AUTOQ::Automata<AUTOQ::Symbol::Symbolic> aut;
        std::map<typename AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State, AUTOQ::Symbol::Symbolic> states_probs;
        AUTOQ::Complex::SymbolicComplex default_prob;
        const std::regex myregex("(.*?)\\|(.*?)>");
        const std::regex_iterator<std::string::iterator> END;
        std::regex_iterator<std::string::iterator> it2(tree.begin(), tree.end(), myregex);
        while (it2 != END) { // c1|10> + c2|11> + c0|*>
            std::string state = it2->str(2); // 10
            std::string t = it2->str(1); // c1
            std::erase(t, ' ');
            if (!t.empty() && t.at(0) == '+') t = t.substr(1);
            if (t.empty()) t = "1";
            else if (t == "-") t = "-1";
            if (states_probs.empty()) {
                if (state == "*")
                    THROW_AUTOQ_ERROR("The numbers of qubits are not specified!");
                aut.qubitNum = state.length();
            } else if (state != "*" && ((aut.qubitNum < 0) || (static_cast<std::size_t>(aut.qubitNum) != state.length())))
                THROW_AUTOQ_ERROR("The numbers of qubits are not the same in all basis states!");
            // } else if constexpr(std::is_same_v<AUTOQ::Symbol::Symbolic, AUTOQ::SymbolicAutomata::Symbol>) {
            AUTOQ::Complex::SymbolicComplex &symbolic_complex = std::invoke([&]()-> AUTOQ::Complex::SymbolicComplex& {
                if (state == "*") {
                    return default_prob;
                } else {
                    AUTOQ::SymbolicAutomata::State s = std::stoll(state, nullptr, 2);
                    return states_probs[s].complex;
                }
            });
            // auto it = constants.find(t);
            // auto cp = ComplexParser(t, constants);
            // if (cp.getVariable().empty())
            //     symbolic_complex[ComplexParser(t, constants).getComplex()] = {{"1", 1}};
            // else {
            //     if (it == constants.end()) { // is a variable
            //         aut.vars.insert(t + "A");
            //         aut.vars.insert(t + "B");
            //         aut.vars.insert(t + "C");
            //         aut.vars.insert(t + "D");
            //         symbolic_complex[AUTOQ::Complex::Complex::One()] = {{t + "A", 1}};
            //         symbolic_complex[AUTOQ::Complex::Complex::Angle(boost::rational<boost::multiprecision::cpp_int>(1, 8))] = {{t + "B", 1}};
            //         symbolic_complex[AUTOQ::Complex::Complex::Angle(boost::rational<boost::multiprecision::cpp_int>(2, 8))] = {{t + "C", 1}};
            //         symbolic_complex[AUTOQ::Complex::Complex::Angle(boost::rational<boost::multiprecision::cpp_int>(3, 8))] = {{t + "D", 1}};
            //     }
            //     else // is a complex number
            //         symbolic_complex[it -> second] = {{"1", 1}};
            // }
            AUTOQ::Parsing::SymbolicComplexParser scp(t, constants);
            symbolic_complex += scp.getSymbolicComplex();
            for (const auto &var: scp.getNewVars())
                aut.vars.insert(var);
            ++it2;
        }
        typename AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State pow_of_two = 1;
        typename AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State state_counter = 0;
        for (int level=1; level<=aut.qubitNum; level++) {
            for (typename AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State i=0; i<pow_of_two; i++) {
                aut.transitions[typename AUTOQ::Automata<Symbol>::SymbolTag(AUTOQ::Symbol::Symbolic(level), typename AUTOQ::Automata<Symbol>::Tag(1))][state_counter].insert({(state_counter<<1)+1, (state_counter<<1)+2});
                state_counter++;
            }
            pow_of_two <<= 1;
        }
        for (typename AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State i=state_counter; i<=(state_counter<<1); i++) {
            auto spf = states_probs.find(i-state_counter);
            if (spf == states_probs.end()) {
                // if (default_prob == AUTOQ::Symbol::Symbolic())
                //     THROW_AUTOQ_ERROR("The default amplitude is not specified!");
                aut.transitions[typename AUTOQ::Automata<Symbol>::SymbolTag(AUTOQ::Symbol::Symbolic(default_prob), typename AUTOQ::Automata<Symbol>::Tag(1))][i].insert({{}});
            }
            else
                aut.transitions[typename AUTOQ::Automata<Symbol>::SymbolTag(spf->second, typename AUTOQ::Automata<Symbol>::Tag(1))][i].insert({{}});
        }
        aut.finalStates.push_back(0);
        aut.stateNum = (state_counter<<1) + 1;
        aut.reduce();
        return aut;
    }
    /**************************** PredicateAutomata ****************************/
    else if constexpr(std::is_same_v<Symbol, AUTOQ::PredicateAutomata::Symbol>) {
        AUTOQ::Automata<AUTOQ::Symbol::Predicate> aut;
        std::map<typename AUTOQ::Automata<AUTOQ::Symbol::Predicate>::State, std::string> states_probs;
        std::string default_prob;
        const std::regex myregex("(.*?)\\|(.*?)>");
        const std::regex_iterator<std::string::iterator> END;
        std::regex_iterator<std::string::iterator> it2(tree.begin(), tree.end(), myregex);
        while (it2 != END) { // p1|10> + p2|11> + p3|*>
            std::string state = it2->str(2); // 10
            std::string t = it2->str(1); // p1
            std::erase(t, ' ');
            if (!t.empty() && t.at(0) == '+') t = t.substr(1);
            if (states_probs.empty()) {
                if (state == "*")
                    THROW_AUTOQ_ERROR("The numbers of qubits are not specified!");
                aut.qubitNum = state.length();
            } else if (state != "*" && ((aut.qubitNum < 0) || (static_cast<std::size_t>(aut.qubitNum) != state.length()))) {
                THROW_AUTOQ_ERROR("The numbers of qubits are not the same in all basis states!");
            }
            std::string &predicate = std::invoke([&]()-> std::string& {
                if (state == "*") {
                    return default_prob;
                } else {
                    AUTOQ::SymbolicAutomata::State s = std::stoll(state, nullptr, 2);
                    return states_probs[s];
                }
            });
            if (!predicate.empty()) {
                THROW_AUTOQ_ERROR("The predicate of this state has already been specified!");
            }
            auto it = predicates.find(t);
            if (it == predicates.end()) {
                if (do_not_throw_term_undefined_error) {
                    do_not_throw_term_undefined_error = false;
                    return {};
                }
                THROW_AUTOQ_ERROR("The predicate \"" + t + "\" is not defined yet!");
            }
            predicate = it->second;
            ++it2;
        }
        if (default_prob.empty())
            default_prob = "true";
        typename AUTOQ::Automata<AUTOQ::Symbol::Predicate>::State pow_of_two = 1;
        typename AUTOQ::Automata<AUTOQ::Symbol::Predicate>::State state_counter = 0;
        for (int level=1; level<=aut.qubitNum; level++) {
            for (typename AUTOQ::Automata<AUTOQ::Symbol::Predicate>::State i=0; i<pow_of_two; i++) {
                aut.transitions[typename AUTOQ::Automata<Symbol>::SymbolTag(AUTOQ::Symbol::Predicate(level), typename AUTOQ::Automata<Symbol>::Tag(1))][state_counter].insert({(state_counter<<1)+1, (state_counter<<1)+2});
                state_counter++;
            }
            pow_of_two <<= 1;
        }
        for (typename AUTOQ::Automata<AUTOQ::Symbol::Predicate>::State i=state_counter; i<=(state_counter<<1); i++) {
            auto spf = states_probs.find(i-state_counter);
            if (spf == states_probs.end()) {
                // if (default_prob == AUTOQ::Symbol::Predicate())
                //     THROW_AUTOQ_ERROR("The default amplitude is not specified!");
                aut.transitions[typename AUTOQ::Automata<Symbol>::SymbolTag(AUTOQ::Symbol::Predicate(default_prob.c_str()), typename AUTOQ::Automata<Symbol>::Tag(1))][i].insert({{}});
            }
            else
                aut.transitions[typename AUTOQ::Automata<Symbol>::SymbolTag(AUTOQ::Symbol::Predicate(spf->second.c_str()), typename AUTOQ::Automata<Symbol>::Tag(1))][i].insert({{}});
        }
        aut.finalStates.push_back(0);
        aut.stateNum = (state_counter<<1) + 1;
        aut.reduce();
        return aut;
    } else {
        THROW_AUTOQ_ERROR("The type of Symbol is not supported!");
    }
}

void replaceSubstringWithChar(std::string &str, const std::string &substr, char replacementChar) {
    std::string::size_type pos = 0;
    while ((pos = str.find(substr, pos)) != std::string::npos) {
        str.replace(pos, substr.length(), 1, replacementChar);
        pos += 1;
    }
}
template <typename Symbol>
AUTOQ::Automata<Symbol> from_trees_to_automaton(std::string trees, const std::map<std::string, AUTOQ::Complex::Complex> &constants, const std::map<std::string, std::string> &predicates, bool &do_not_throw_term_undefined_error) {
    AUTOQ::Automata<Symbol> aut_final;
    replaceSubstringWithChar(trees, "\\/", 'V');
    if (std::regex_search(trees, std::regex("(\\\\/|V) *\\|i\\|="))) { // if startswith "\/ |i|="
        std::istringstream iss(trees);
        std::string length;
        std::getline(iss, length, ':');
        length = AUTOQ::String::trim(length.substr(length.find('=') + 1));
        trees.clear();
        for (std::string t; iss >> t;)
            trees += t + ' ';
        std::string i(std::atoi(length.c_str()), '1');
        bool reach_all_zero;
        do {
            std::string ic = i;
            std::replace(ic.begin(), ic.end(), '0', 'x');
            std::replace(ic.begin(), ic.end(), '1', '0');
            std::replace(ic.begin(), ic.end(), 'x', '1');
            const boost::regex pattern(R"(\|[^>]*>)");
            auto replace_ic_with_ic = [&ic](const boost::smatch& match) -> std::string {
                std::string modified_str = match.str();
                return std::regex_replace(modified_str, std::regex("i'"), ic);
            };
            std::string line2 = boost::regex_replace(trees, pattern, replace_ic_with_ic, boost::match_default | boost::format_all);
            auto replace_i_with_i = [&i](const boost::smatch& match) -> std::string {
                std::string modified_str = match.str();
                return std::regex_replace(modified_str, std::regex("i"), i);
            };
            std::string line3 = boost::regex_replace(line2, pattern, replace_i_with_i, boost::match_default | boost::format_all);
            auto a = do_not_throw_term_undefined_error;
            auto aut = from_tree_to_automaton<Symbol>(line3, constants, predicates, do_not_throw_term_undefined_error);
            if (a && !do_not_throw_term_undefined_error) {
                return {};
            }
            aut_final = aut_final.operator||(aut);
            aut_final.reduce();

            // the following performs -1 on the binary string i
            reach_all_zero = false;
            for (int j=i.size()-1; j>=0; j--) {
                if (i.at(j) == '0') {
                    if (j == 0) {
                        reach_all_zero = true;
                        break;
                    }
                    i.at(j) = '1';
                } else {
                    i.at(j) = '0';
                    break;
                }
            }
        } while (!reach_all_zero);
    } else {
        std::istringstream iss_or(trees);
        std::string tree;
        std::getline(iss_or, tree, 'V');

        auto a = do_not_throw_term_undefined_error;
        aut_final = from_tree_to_automaton<Symbol>(tree, constants, predicates, do_not_throw_term_undefined_error); // the first automata to be tensor producted
        if (a && !do_not_throw_term_undefined_error) {
            return {};
        }

        // to union the rest of the automata
        while (std::getline(iss_or, tree, 'V')) {
            auto a = do_not_throw_term_undefined_error;
            auto aut2 = from_tree_to_automaton<Symbol>(tree, constants, predicates, do_not_throw_term_undefined_error);
            if (a && !do_not_throw_term_undefined_error) {
                return {};
            }
            aut_final = aut_final || aut2;
        }
    }
    return aut_final;
}

template <typename Symbol>
AUTOQ::Automata<Symbol> from_line_to_automaton(std::string line, const std::map<std::string, AUTOQ::Complex::Complex> &constants, const std::map<std::string, std::string> &predicates, bool &do_not_throw_term_undefined_error) {
    std::istringstream iss_tensor(line);
    std::string trees;
    std::getline(iss_tensor, trees, '#');

    auto a = do_not_throw_term_undefined_error;
    auto aut = from_trees_to_automaton<Symbol>(trees, constants, predicates, do_not_throw_term_undefined_error); // the first automata to be tensor producted
    if (a && !do_not_throw_term_undefined_error) {
        return {};
    }

    // to tensor product with the rest of the automata
    while (std::getline(iss_tensor, trees, '#')) {
        auto a = do_not_throw_term_undefined_error;
        auto aut2 = from_trees_to_automaton<Symbol>(trees, constants, predicates, do_not_throw_term_undefined_error);
        if (a && !do_not_throw_term_undefined_error) {
            return {};
        }
        aut = aut * aut2;
    }
    return aut;
}

/**
 * @brief  Parse a string with Timbuk definition of an automaton
 */
template <typename Symbol>
typename AUTOQ::Automata<Symbol>::Symbol parse_symbol(const std::string& str, std::set<std::string> &vars) {
    /************************** TreeAutomata **************************/
    if constexpr(std::is_same_v<Symbol, AUTOQ::TreeAutomata::Symbol>) {
        if constexpr(std::is_same_v<Complex, AUTOQ::Complex::FiveTuple>) {
            std::vector<boost::multiprecision::cpp_int> temp;
            temp.clear();
            if (str[0] == '[') {
                for (int i=1; i<static_cast<int>(str.length()); i++) {
                    size_t j = str.find(',', i);
                    if (j == std::string::npos) j = str.length()-1;
                    try {
                        temp.push_back(boost::lexical_cast<boost::multiprecision::cpp_int>(str.substr(i, j-i).c_str()));
                    } catch (...) {
                        THROW_AUTOQ_ERROR("The input entry \"" + str.substr(i, j-i) + "\" is not an integer!");
                    }
                    i = j;
                }
            } else {
                try {
                    temp.push_back(boost::lexical_cast<boost::multiprecision::cpp_int>(str.c_str()));
                } catch (...) {
                    THROW_AUTOQ_ERROR("The input entry \"" + str + "\" is not an integer!");
                }
            }
            assert(temp.size() == 1 || temp.size() == 5);
            if (temp.size() == 1) return AUTOQ::TreeAutomata::Symbol(temp.at(0));
            return AUTOQ::TreeAutomata::Symbol(temp);
        } else {
            THROW_AUTOQ_ERROR("The type of Complex is not supported!");
        }
    }
    /**************************** SymbolicAutomata ****************************/
    else if constexpr(std::is_same_v<Symbol, AUTOQ::SymbolicAutomata::Symbol>) {
        std::string str2 = str.substr(str.front()=='[', str.length() - (str.front()=='[') - (str.back()==']'));
        try {
            return AUTOQ::SymbolicAutomata::Symbol(boost::lexical_cast<boost::multiprecision::cpp_int>(str2.c_str()));
        } catch (boost::bad_lexical_cast& e) {
            auto sp = AUTOQ::Parsing::SymbolicComplexParser(str2);
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
                        AUTOQ::Parsing::SymbolicComplexParser scp(token, constants);
                        auto sym = Symbol(scp.getSymbolicComplex());
                        std::getline(ss, token, ',');
                        auto color = boost::lexical_cast<AUTOQ::SymbolicAutomata::Tag>(token);
                        result.transitions[AUTOQ::SymbolicAutomata::SymbolTag(sym, AUTOQ::SymbolicAutomata::Tag(color))][t].insert(std::vector<AUTOQ::SymbolicAutomata::State>());
                        for (const auto &var: scp.getNewVars())
                            result.vars.insert(var);
                    } else {
                        AUTOQ::Parsing::SymbolicComplexParser scp(lhs, constants);
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

template <typename Symbol>
AUTOQ::Automata<Symbol> AUTOQ::Parsing::TimbukParser<Symbol>::parse_hsl_from_istream(std::istream *is, bool &do_not_throw_term_undefined_error, const std::map<std::string, AUTOQ::Complex::Complex> &constants, const std::map<std::string, std::string> &predicates) {
    bool start_transitions = false;
    AUTOQ::Automata<Symbol> aut_final;
    std::string line;
    while (std::getline(*is, line)) {
		line = AUTOQ::String::trim(line);
		if (line.empty()) { continue; }
		if (!start_transitions) {
            if (std::regex_search(line, std::regex("Extended +Dirac"))) {
                start_transitions = true;
                continue;
            }
        }   // processing states
        else {
            auto a = do_not_throw_term_undefined_error;
            auto aut = from_line_to_automaton<Symbol>(line, constants, predicates, do_not_throw_term_undefined_error);
            if (a && !do_not_throw_term_undefined_error) {
                return {};
            }
            aut_final = aut_final.operator||(aut);
            aut_final.reduce();
        }
    }
    // DO NOT fraction_simplification() here since the resulting automaton may be used as pre.lsta
    // and in this case all k's must be the same.
    return aut_final;
}

template <typename Symbol>
AUTOQ::Automata<Symbol> parse_hsl(const std::string& str, const std::map<std::string, Complex> &constants, const std::map<std::string, std::string> &predicates, bool &do_not_throw_term_undefined_error) {
    std::istringstream inputStream(str); // delimited by '\n'
    auto aut = AUTOQ::Parsing::TimbukParser<Symbol>::parse_hsl_from_istream(&inputStream, do_not_throw_term_undefined_error, constants, predicates);
    // aut.print(str);
    return aut;
}

// template <typename Symbol>
// AUTOQ::Automata<Symbol> AUTOQ::Parsing::TimbukParser<Symbol>::ReadAutomaton(const std::string& filepath) {
//     return ParseString(AUTOQ::Util::ReadFile(filepath));
// }
template <typename Symbol>
AUTOQ::Automata<Symbol> AUTOQ::Parsing::TimbukParser<Symbol>::ReadAutomaton(const std::string& filepath) {
    bool do_not_throw_term_undefined_error = false;
    return AUTOQ::Parsing::TimbukParser<Symbol>::ReadAutomaton(filepath, do_not_throw_term_undefined_error);
}
template <typename Symbol>
AUTOQ::Automata<Symbol> AUTOQ::Parsing::TimbukParser<Symbol>::ReadAutomaton(const std::string& filepath, bool &do_not_throw_term_undefined_error) {
try {
    AUTOQ::Automata<Symbol> result;
    std::string automaton, constraints;
    std::string fileContents = AUTOQ::Util::ReadFile(filepath);
    std::map<std::string, AUTOQ::Complex::Complex> constants;
    std::map<std::string, std::string> predicates;

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
        (fileContents.find("Constants") != std::string::npos ||
         fileContents.find("Predicates") != std::string::npos)) {
        size_t found2 = std::min(fileContents.find("Extended"), fileContents.find("Root"));
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
                        constants[lhs] = ComplexParser(rhs).getComplex();
                    } else {
                        THROW_AUTOQ_ERROR("The constant \"" + lhs + "\" is already defined.");
                    }
                }
            }
        }
        if (fileContents.find("Predicates") != std::string::npos) {
            std::string predicates_str = AUTOQ::String::trim(fileContents.substr(std::string("Predicates").length(), found2 - std::string("Predicates").length()));
            fileContents = fileContents.substr(found2);
            std::stringstream ss(predicates_str);
            std::string str;
            while (std::getline(ss, str, '\n')) {
                size_t arrow_pos = str.find(":=");
                if (std::string::npos != arrow_pos) { // Variables may appear without values in the symbolic case.
                    std::string lhs = AUTOQ::String::trim(str.substr(0, arrow_pos));
                    std::string rhs = AUTOQ::String::trim(str.substr(arrow_pos + 2));
                    if (lhs.empty() || rhs.empty()) {
                        THROW_AUTOQ_ERROR("Invalid number \"" + str + "\".");
                    }
                    if (predicates.find(lhs) == predicates.end()) {
                        predicates[lhs] = rhs;
                    } else {
                        THROW_AUTOQ_ERROR("The predicate \"" + lhs + "\" is already defined.");
                    }
                }
            }
        }

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
                for (int i=0; i<4; i++)
                    kv.second.at(i) <<= static_cast<int>((max_k - kv.second.at(4)) / 2);
                kv.second.at(4) = max_k;
            }
        }
        #endif

        #ifdef COMPLEX_nTuple
        // Unify k's for all complex numbers if n-tuple is used
        // for speeding up binary operations.
        boost::multiprecision::cpp_int max_k = INT_MIN;
        for (const auto &kv : constants) {
            if (!kv.second.empty())
                if (max_k < kv.second.k)
                    max_k = kv.second.k;
        }
        if (max_k == INT_MIN) max_k = 0; // IMPORTANT: if not modified, resume to 0.
        for (auto &kv : constants) {
            if (kv.second.empty())
                kv.second.k = max_k;
            else {
                for (auto &kv2 : kv.second)
                    kv2.second <<= static_cast<int>((max_k - kv.second.k) / 2);
                kv.second.k = max_k;
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
        result = parse_automaton<Symbol>(automaton, constants, predicates, do_not_throw_term_undefined_error);
    } else if (boost::algorithm::ends_with(filepath, ".aut")) {
        result = parse_timbuk<Symbol>(automaton);
    } else if (boost::algorithm::ends_with(filepath, ".hsl")) {
        result = parse_hsl<Symbol>(automaton, constants, predicates, do_not_throw_term_undefined_error);
    } else {
        THROW_AUTOQ_ERROR("The filename extension is not supported.");
    }

    std::stringstream ss(AUTOQ::String::trim(constraints));
    std::string constraint;
    while (std::getline(ss, constraint, '\n')) {
        result.constraints += ConstraintParser(constraint, constants).getSMTexpression();
    }
    if (!result.constraints.empty())
        result.constraints = "(assert (and " + result.constraints + "))";
    for (const auto &var : result.vars) {
        result.constraints = "(declare-const " + var + " Real)" + result.constraints;
    }
    return result;
} catch (AutoQError &e) {
    std::cout << e.what() << std::endl;
    THROW_AUTOQ_ERROR("(while parsing the automaton: " + filepath + ")");
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

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>;
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>;
