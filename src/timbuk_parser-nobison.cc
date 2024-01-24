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

// AUTOQ headers
#include <autoq/autoq.hh>
#include <autoq/util/util.hh>
#include <autoq/complex/complex.hh>
#include <autoq/complex/fivetuple.hh>
#include <autoq/symbol/concrete.hh>
#include <autoq/symbol/symbolic.hh>
#include <autoq/symbol/predicate.hh>
#include <autoq/parsing/timbuk_parser.hh>
#include <autoq/parsing/complex_parser.hh>
#include <autoq/parsing/linearcombination_parser.hh>
#include <autoq/aut_description.hh>
#include <boost/algorithm/string/predicate.hpp>

using AUTOQ::Parsing::TimbukParser;
using AUTOQ::Symbol::Concrete;
using AUTOQ::Symbol::Symbolic;
using AUTOQ::Symbol::Predicate;
using AUTOQ::Automata;
using AUTOQ::TreeAutomata;
using AUTOQ::SymbolicAutomata;
using AUTOQ::PredicateAutomata;
using AUTOQ::Util::Convert;
using AUTOQ::Util::trim;
using AUTOQ::Complex::Complex;
using AUTOQ::Parsing::LinearCombinationParser;

/**
 * @brief  Split a string at a delimiter
 */
static std::vector<std::string> split_delim(
	const std::string&   str,
	char                 delim)
{
	std::vector<std::string> result;

	std::string::size_type pos = 0;
	std::string::size_type prev = 0;
	while ((pos = str.find(delim, prev)) != std::string::npos)
	{
		result.push_back(str.substr(prev, pos - prev));
		prev = pos + 1;
	}

	// To get the last substring (or only, if delimiter is not found)
	result.push_back(str.substr(prev));

	return result;
}


/**
 * @brief  Read the first word from a string
 *
 * Reads the first word from a string and removes it from there
 */
static std::string read_word(std::string& str)
{
	std::string::iterator end(std::find_if(str.begin(), str.end(),
		[](int ch) { return std::isspace(ch);}));
	std::string result(str.begin(), end);

	str.erase(str.begin(), end);
	str = trim(str);
	return result;
}


/**
 * @brief  Does the string contain a whitespace?
 */
static bool contains_whitespace(const std::string& str)
{
	return str.end() != std::find_if(str.begin(), str.end(), [](int ch) { return std::isspace(ch);});
}


/**
 * @brief  Parse a token of the form <string>:<number> or <string>
 */
static std::pair<std::string, int> parse_colonned_token(std::string str)
{
	str = trim(str);

	// no space inside
	assert(!contains_whitespace(str));

	size_t colon_pos = str.find(":");
	if (std::string::npos == colon_pos)
	{	// no colon found
		return std::make_pair(str, -1);
	}
	else
	{	// colon found
		std::string number_str = str.substr(colon_pos + 1);

		return std::make_pair(str.substr(0, colon_pos), Convert::FromString<int>(number_str));
	}
}

/**
 * @brief  Parse a string with Timbuk definition of an automaton
 */
typename TreeAutomata::Symbol from_string_to_Concrete(const std::string& str)
{
	Complex temp;
    if (str[0] == '[') {
        for (int i=1; i<static_cast<int>(str.length()); i++) {
            size_t j = str.find(',', i);
            if (j == std::string::npos) j = str.length()-1;
            try {
                temp.push_back(boost::lexical_cast<boost::multiprecision::cpp_int>(str.substr(i, j-i).c_str()));
            } catch (...) {
                throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] The input entry \"" + str.substr(i, j-i) + "\" is not an integer!");
            }
            i = j;
        }
    } else {
        try {
            temp.push_back(boost::lexical_cast<boost::multiprecision::cpp_int>(str.c_str()));
        } catch (...) {
            throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] The input entry \"" + str + "\" is not an integer!");
        }
    }
    assert(temp.size() == 1 || temp.size() == 5);
    if (temp.size() == 1) return TreeAutomata::Symbol(temp.at(0));
    // if (temp.size() == 5)
    return TreeAutomata::Symbol(temp);
}

SymbolicAutomata::Symbol from_string_to_Symbolic(const std::string& str)
{
	std::vector<AUTOQ::Symbol::linear_combination> temp;
    if (str[0] == '[') {
        for (int i=1; i<static_cast<int>(str.length()); i++) {
            size_t j = str.find(',', i);
            if (j == std::string::npos) j = str.length()-1;
            try {
                auto sp = LinearCombinationParser(str.substr(i, j-i));
                // auto v = boost::lexical_cast<boost::multiprecision::cpp_int>(str.substr(i, j-i).c_str());
                // if (v == 0)
                //     temp.push_back(AUTOQ::Symbol::linear_combination());
                // else
                    temp.push_back(sp.parse()); //{{"1", v}});
            } catch (boost::bad_lexical_cast& e) {
                temp.push_back({{str.substr(i, j-i).c_str(), 1}});
            }
            i = j;
        }
    } else {
        try {
            auto sp = LinearCombinationParser(str);
            // auto v = boost::lexical_cast<boost::multiprecision::cpp_int>(str.c_str());
            // if (v == 0)
            //     temp.push_back(AUTOQ::Symbol::linear_combination());
            // else
                temp.push_back(sp.parse()); //{{"1", v}});
        } catch (boost::bad_lexical_cast& e) {
            temp.push_back({{str.c_str(), 1}});
        }
    }
    if (temp.size() == 5) return SymbolicAutomata::Symbol({{Complex::Angle(0).divide_by_the_square_root_of_two(static_cast<int>(temp.at(4).at("1"))), temp.at(0)},
                                                           {Complex::Angle(boost::rational<boost::multiprecision::cpp_int>(1, 8)).divide_by_the_square_root_of_two(static_cast<int>(temp.at(4).at("1"))), temp.at(1)},
                                                           {Complex::Angle(boost::rational<boost::multiprecision::cpp_int>(2, 8)).divide_by_the_square_root_of_two(static_cast<int>(temp.at(4).at("1"))), temp.at(2)},
                                                           {Complex::Angle(boost::rational<boost::multiprecision::cpp_int>(3, 8)).divide_by_the_square_root_of_two(static_cast<int>(temp.at(4).at("1"))), temp.at(3)}});
    assert(temp.size() == 1);
    const auto &tt = temp.at(0);
    if (tt.find("1") != tt.end() && tt.at("1") > 0)
        return SymbolicAutomata::Symbol(static_cast<int>(tt.at("1")));
    else
        return SymbolicAutomata::Symbol({{Complex::One(), tt}});
}

PredicateAutomata::Symbol from_string_to_Predicate(const std::string& lhs)
{
    try {
        return Predicate(boost::multiprecision::cpp_int(lhs.substr(1, lhs.size()-2)));
    } catch (...) {
        return Predicate(lhs.substr(1, lhs.size()-2).c_str());
    }
}

template <typename Symbol>
Automata<Symbol> parse_timbuk(const std::string& str) {
	Automata<Symbol> result;

	bool are_transitions = false;
	bool aut_parsed = false;
	// bool ops_parsed = false;
	bool states_parsed = false;
	bool final_parsed = false;

	std::vector<std::string> lines = split_delim(str, '\n');
	for (const std::string& line : lines)
	{
		std::string str = trim(line);
		if (str.empty()) { continue; }

		if (!are_transitions)
		{
			std::string first_word = read_word(str);
			if ("Transitions" == first_word)
			{
				are_transitions = true;
				continue;
			}
			else if ("Automaton" == first_word)
			{
				if (aut_parsed)
				{
					throw std::runtime_error(AUTOQ_LOG_PREFIX + "Automaton already parsed!");
				}

				aut_parsed = true;

				result.name = read_word(str);

				if (!str.empty())
				{
					throw std::runtime_error(AUTOQ_LOG_PREFIX + "Line \"" + line +
						"\" has an unexpected string.");
				}
			}
			else if ("Ops" == first_word)
			{
				// if (ops_parsed)
				// {
				// 	throw std::runtime_error(AUTOQ_LOG_PREFIX + "Ops already parsed!");
				// }

				// ops_parsed = true;

				// while (!str.empty())
				// {
				// 	std::string label = read_word(str);
				// 	auto label_num = parse_colonned_token(label);
                //     auto temp = symbol_converter<Symbol>(label_num.first);

				// 	// result.symbols[temp] = label_num.second;
				// }
			}
			else if ("States" == first_word)
			{
				if (states_parsed)
				{
					throw std::runtime_error(AUTOQ_LOG_PREFIX + "States already parsed!");
				}

				states_parsed = true;

				// while (!str.empty())
				// {
				// 	std::string state = read_word(str);
				// 	auto state_num = parse_colonned_token(state);
				// 	// result.states.insert(state_num.first);
                //     /****************************************************************************************/
                //     // assert(result.stateNum.FindFwd(state_num.first) == result.stateNum.end());
                //     result.stateNum++; //.insert(std::make_pair(state_num.first, result.stateNum.size()));
                //     /****************************************************************************************/
				// }
			}
			else if ("Final" == first_word)
			{
				std::string str_states = read_word(str);
				if ("States" != str_states)
				{
					throw std::runtime_error(AUTOQ_LOG_PREFIX + "Line \"" + line +
						"\" contains an unexpected string.");
				}

				if (final_parsed)
				{
					throw std::runtime_error(AUTOQ_LOG_PREFIX + "Final States already parsed!");
				}

				final_parsed = true;

				while (!str.empty())
				{
					std::string state = read_word(str);
					auto state_num = parse_colonned_token(state);
					// result.finalStates.insert(state_num.first);
                    /****************************************************************************/
                    int t = atoi(state_num.first.c_str());
                    if (t > result.stateNum) result.stateNum = t;
                    result.finalStates.insert(t); //result.stateNum.TranslateFwd(state_num.first));
                    /****************************************************************************/
				}
			}
			else
			{	// guard
				throw std::runtime_error(AUTOQ_LOG_PREFIX + "Line \"" + line +
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
				throw std::runtime_error(invalid_trans_str);
			}

			std::string lhs = trim(str.substr(0, arrow_pos));
			std::string rhs = trim(str.substr(arrow_pos + 2));

			if (rhs.empty() ||
				contains_whitespace(rhs))
			{
				throw std::runtime_error(invalid_trans_str);
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
					(!std::is_same_v<Symbol, PredicateAutomata::Symbol> && contains_whitespace(lhs)) ||
					lhs.empty())
				{
					throw std::runtime_error(invalid_trans_str);
				}

				// result.transitions.insert(TreeAutomata::Transition({}, lhs, rhs));
                /*******************************************************************************************************************/
                int t = atoi(rhs.c_str());
                if (t > result.stateNum) result.stateNum = t;
                if constexpr(std::is_same_v<Symbol, TreeAutomata::Symbol>) {
                    auto temp = from_string_to_Concrete(lhs);
                    result.transitions[temp][t].insert(std::vector<TreeAutomata::State>()); //.stateNum.TranslateFwd(rhs));
                } else if constexpr(std::is_same_v<Symbol, PredicateAutomata::Symbol>) {
                    auto temp = from_string_to_Predicate(lhs);
                    result.transitions[temp][t].insert(std::vector<TreeAutomata::State>()); //.stateNum.TranslateFwd(rhs));
                } else {
                    auto temp = from_string_to_Symbolic(lhs);
                    result.transitions[temp][t].insert(std::vector<SymbolicAutomata::State>()); //.stateNum.TranslateFwd(rhs));
                }
                /*******************************************************************************************************************/
			}
			else
			{	// contains a tuple of states
				if ((std::string::npos == parens_end_pos) ||
					(parens_begin_pos > parens_end_pos) ||
					(parens_end_pos != lhs.length() - 1))
				{
					throw std::runtime_error(invalid_trans_str);
				}

				std::string lab = trim(lhs.substr(0, parens_begin_pos));

				if (lab.empty())
				{
					throw std::runtime_error(invalid_trans_str);
				}

				std::string str_state_tuple = lhs.substr(parens_begin_pos + 1,
					parens_end_pos - parens_begin_pos - 1);

				/********************************************/
                std::vector<typename Automata<Symbol>::State> state_vector;
                /********************************************/
                std::vector<std::string> state_tuple = split_delim(str_state_tuple, ',');
				for (std::string& state : state_tuple)
				{
					state = trim(state);

					if (contains_whitespace(state))
					{
						throw std::runtime_error(invalid_trans_str);
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

				// result.transitions.insert(TreeAutomata::Transition(state_tuple, lab, rhs));
                /*********************************************************************************************/
                int t = atoi(rhs.c_str());
                if (t > result.stateNum) result.stateNum = t;
                if constexpr(std::is_same_v<Symbol, TreeAutomata::Symbol>) {
                    auto temp = from_string_to_Concrete(lab);
                    result.transitions[temp][t].insert(state_vector); //result.stateNum.TranslateFwd(rhs));
                } else if constexpr(std::is_same_v<Symbol, PredicateAutomata::Symbol>) {
                    auto temp = from_string_to_Predicate(lab);
                    result.transitions[temp][t].insert(state_vector); //.stateNum.TranslateFwd(rhs));
                } else {
                    auto temp = from_string_to_Symbolic(lab);
                    result.transitions[temp][t].insert(state_vector); //result.stateNum.TranslateFwd(rhs));
                }
                /*********************************************************************************************/
			}
		}
	}

	if (!are_transitions)
	{
		throw std::runtime_error(AUTOQ_LOG_PREFIX + "Transitions not specified.");
	}

    for (const auto &kv : result.transitions) {
        if (kv.first.is_internal()) {
            if (kv.first.symbol().qubit() > INT_MAX)
                throw std::overflow_error(AUTOQ_LOG_PREFIX + "[ERROR] The number of qubits is too large!");
            result.qubitNum = std::max(result.qubitNum, static_cast<unsigned>(kv.first.symbol().qubit()));
        }
    }
    result.stateNum++;
	return result;
}

template <typename Symbol>
Automata<Symbol> parse_automaton(const std::string& str) {
try {
	bool start_numbers = false;
    bool start_transitions = false;
    Automata<Symbol> result;
    std::map<std::string, Complex> numbers;
    std::map<std::string, std::string> predicates;
    std::map<std::string, typename Automata<Symbol>::State> states;

	std::vector<std::string> lines = split_delim(str, '\n');
	for (const std::string& line : lines) {
		std::string str = trim(line);
		if (str.empty()) { continue; }

		if (!start_numbers) {
			std::string first_word = read_word(str);
            if constexpr(std::is_same_v<Symbol, Predicate>) {
                if ("Predicates" == first_word) {
                    start_numbers = true;
                    continue;
                } else {	// guard
                    throw std::runtime_error(AUTOQ_LOG_PREFIX + "Line \"" + line +
                        "\" contains an unexpected string.");
                }
            } else {
                if ("Numbers" == first_word) {
                    start_numbers = true;
                    continue;
                } else {	// guard
                    throw std::runtime_error(AUTOQ_LOG_PREFIX + "Line \"" + line +
                        "\" contains an unexpected string.");
                }
            }
		} else if (!start_transitions) {	// processing numbers
            if (str == "Transitions") {
                start_transitions = true;
                continue;
            }

            size_t arrow_pos = str.find(":=");
			if (std::string::npos != arrow_pos) { // Variables may appear without values in the symbolic case.
                std::string lhs = trim(str.substr(0, arrow_pos));
                std::string rhs = trim(str.substr(arrow_pos + 2));
                if (lhs.empty() || rhs.empty()) {
                    if constexpr(std::is_same_v<Symbol, Predicate>)
                        throw std::runtime_error(AUTOQ_LOG_PREFIX + "Invalid predicate \"" + line + "\".");
                    else
                        throw std::runtime_error(AUTOQ_LOG_PREFIX + "Invalid number \"" + line + "\".");
                }
                if constexpr(!std::is_same_v<Symbol, Predicate>) {
                    numbers[lhs] = ComplexParser(rhs).getComplex();
                    // std::cout << lhs << " " << numbers[lhs] << "\n";
                } else
                    predicates[lhs] = rhs;
            }
        } else {	// processing transitions
            #ifdef COMPLEX_FiveTuple
            // Unify k's for all complex numbers if 5-tuple is used
            // for speeding up binary operations.
            boost::multiprecision::cpp_int max_k = INT_MIN;
            if constexpr(std::is_same_v<Complex, AUTOQ::Complex::FiveTuple>) {
                for (const auto &kv : numbers) {
                    if (kv.second.at(0)!=0 || kv.second.at(1)!=0 || kv.second.at(2)!=0 || kv.second.at(3)!=0)
                        if (max_k < kv.second.at(4))
                            max_k = kv.second.at(4);
                }
                if (max_k == INT_MIN) max_k = 0; // IMPORTANT: if not modified, resume to 0.
                for (auto &kv : numbers) {
                    if (kv.second.at(0)==0 && kv.second.at(1)==0 && kv.second.at(2)==0 && kv.second.at(3)==0)
                        kv.second.at(4) = max_k;
                    else {
                        for (int i=0; i<4; i++)
                            kv.second.at(i) <<= static_cast<int>((max_k - kv.second.at(4)) / 2);
                        kv.second.at(4) = max_k;
                    }
                }
            }
            #endif

			std::string invalid_trans_str = AUTOQ_LOG_PREFIX +
				"Invalid transition \"" + line + "\".";

			size_t arrow_pos = str.find("->");
			if (std::string::npos == arrow_pos) {
				throw std::runtime_error(invalid_trans_str);
			}

			std::string lhs = trim(str.substr(0, arrow_pos));
			std::string rhs = trim(str.substr(arrow_pos + 2));
			if (rhs.empty() || contains_whitespace(rhs)) {
				throw std::runtime_error(invalid_trans_str);
			}

			size_t parens_begin_pos = lhs.find("(");
			size_t parens_end_pos = lhs.find(")");
            if (parens_begin_pos < lhs.find("]"))
                parens_begin_pos = std::string::npos;
            if (parens_end_pos < lhs.find("]"))
                parens_end_pos = std::string::npos;
			if (std::string::npos == parens_begin_pos) {	// no tuple of states -> leaf
				if ((std::string::npos != parens_end_pos) ||
					(!std::is_same_v<Symbol, PredicateAutomata::Symbol> && contains_whitespace(lhs)) ||
					lhs.empty()) {
					throw std::runtime_error(invalid_trans_str);
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
                if constexpr(std::is_same_v<Symbol, TreeAutomata::Symbol>) {
                    try {
                        result.transitions[Symbol(boost::lexical_cast<int>(lhs))][t].insert(std::vector<TreeAutomata::State>());
                    } catch (...) {
                        result.transitions[Symbol(numbers.at(lhs))][t].insert(std::vector<TreeAutomata::State>());
                    }
                } else if constexpr(std::is_same_v<Symbol, PredicateAutomata::Symbol>) {
                    try {
                        result.transitions[Symbol(boost::lexical_cast<int>(lhs))][t].insert(std::vector<TreeAutomata::State>());
                    } catch (...) {
                        result.transitions[Symbol(predicates.at(lhs).c_str())][t].insert(std::vector<TreeAutomata::State>());
                    }
                } else { // if constexpr(std::is_same_v<Symbol, SymbolicAutomata::Symbol>) {
                    try {
                        result.transitions[Symbol(boost::lexical_cast<int>(lhs))][t].insert(std::vector<SymbolicAutomata::State>());
                    } catch (...) {
                        try {
                            if (numbers.at(lhs).isZero())
                                result.transitions[Symbol()][t].insert(std::vector<SymbolicAutomata::State>());
                            else
                                result.transitions[Symbol({{numbers.at(lhs), {{"1", 1}}}})][t].insert(std::vector<SymbolicAutomata::State>());
                        } catch (...) {
                            result.transitions[Symbol({{Complex::One(), {{lhs, 1}}}})][t].insert(std::vector<SymbolicAutomata::State>());
                        }
                    }
                }
                /*******************************************************************************************************************/
			} else {	// contains a tuple of states -> internal
				if ((std::string::npos == parens_end_pos) ||
					(parens_begin_pos > parens_end_pos) ||
					(parens_end_pos != lhs.length() - 1)) {
					throw std::runtime_error(invalid_trans_str);
				}

				std::string symbol = trim(lhs.substr(0, parens_begin_pos));
				if (symbol.empty()) {
					throw std::runtime_error(invalid_trans_str);
				}

                std::vector<typename Automata<Symbol>::State> state_vector;
                std::string str_state_tuple = lhs.substr(parens_begin_pos + 1,
					parens_end_pos - parens_begin_pos - 1);
                std::vector<std::string> state_tuple = split_delim(str_state_tuple, ',');
				for (std::string& state : state_tuple) {
					state = trim(state);
					if (contains_whitespace(state)) {
						throw std::runtime_error(invalid_trans_str);
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
                if (symbol == "[1]")
                    result.finalStates.insert(t);
                if constexpr(std::is_same_v<Symbol, TreeAutomata::Symbol>) {
                    result.transitions[Symbol(boost::lexical_cast<int>(symbol.substr(1, symbol.length()-2)))][t].insert(state_vector);
                    if (boost::lexical_cast<int>(symbol.substr(1, symbol.length()-2)) == 1)
                        result.finalStates.insert(t);
                } else if constexpr(std::is_same_v<Symbol, PredicateAutomata::Symbol>) {
                    auto temp = from_string_to_Predicate(symbol);
                    result.transitions[temp][t].insert(state_vector);
                    if (boost::lexical_cast<int>(temp.qubit()) == 1)
                        result.finalStates.insert(t);
                } else {
                    auto temp = from_string_to_Symbolic(symbol);
                    result.transitions[temp][t].insert(state_vector);
                    if (boost::lexical_cast<int>(temp.qubit()) == 1)
                        result.finalStates.insert(t);
                }
                /*********************************************************************************************/
			}
		}
	}

	if (!start_transitions) {
		throw std::runtime_error(AUTOQ_LOG_PREFIX + "Transitions not specified.");
	}

    for (const auto &kv : result.transitions) {
        if (kv.first.is_internal()) {
            if (kv.first.symbol().qubit() > INT_MAX)
                throw std::overflow_error(AUTOQ_LOG_PREFIX + "[ERROR] The number of qubits is too large!");
            result.qubitNum = std::max(result.qubitNum, static_cast<unsigned>(kv.first.symbol().qubit()));
        }
    }
    result.stateNum++; // because the state number starts from 0
	return result;
} catch (std::exception& ex) {
    throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] \'" + std::string(ex.what()) +
        "\'\nwhile parsing the following automaton.\n\n>>>>>>>>>>>>>>>>>>>>\n" + str + "\n<<<<<<<<<<<<<<<<<<<<");
}
}

template <typename Symbol>
Automata<Symbol> TimbukParser<Symbol>::parse_hsl_from_istream(std::istream *is) {
    Automata<Symbol> aut_final;
    std::string line;
    while (std::getline(*is, line)) {
        line = AUTOQ::Util::trim(line);
        if (line.empty()) continue;
        if (line.substr(0, 4) == "|i|=") { // if startswith "|i|="
            std::istringstream iss(line);
            std::string length; iss >> length; length = length.substr(4);
            line.clear();
            for (std::string t; iss >> t;)
                line += t + ' ';
            std::string i(std::atoi(length.c_str()), '1');
            bool reach_all_zero;
            do {
                auto aut = TimbukParser<Symbol>::from_line_to_automaton(std::regex_replace(line, std::regex("i:"), i + ":"));
                aut_final = aut_final.Union(aut);
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
            auto aut = TimbukParser<Symbol>::from_line_to_automaton(line);
            aut_final = aut_final.Union(aut);
            aut_final.reduce();
        }
    }
    // DO NOT fraction_simplification() here since the resulting automaton may be used as pre.spec
    // and in this case all k's must be the same.
    return aut_final;
}

template <typename Symbol>
Automata<Symbol> parse_hsl(const std::string& str) {
    std::istringstream inputStream(str); // delimited by '\n'
    return TimbukParser<Symbol>::parse_hsl_from_istream(&inputStream);
}

template <> // The loop reading part is different from other types, so we have to specialize this type.
PredicateAutomata TimbukParser<Predicate>::from_tree_to_automaton(std::string tree) {
    PredicateAutomata aut;
    std::map<PredicateAutomata::State, PredicateAutomata::Symbol> states_probs;
    PredicateAutomata::Symbol default_prob;
    std::smatch match;
    while (std::regex_search(tree, match, std::regex("\\[.*?\\]"))) {
        std::string state_prob = match.str();
        tree = match.suffix().str(); // notice that the order of this line and the above line cannot be reversed!
        state_prob = state_prob.substr(1, state_prob.size()-2);
        std::istringstream iss2(state_prob);
        std::string state;
        std::getline(iss2, state, ':');
        if (states_probs.empty())
            aut.qubitNum = state.length();
        std::string t;
        if (state == "*") {
            std::getline(iss2, t);
            default_prob = Predicate(t.c_str());
        } else {
            PredicateAutomata::State s = std::stoll(state, nullptr, 2);
            auto &sps = states_probs[s];
            std::getline(iss2, t);
            sps = Predicate(t.c_str());
        }
    }
    PredicateAutomata::State pow_of_two = 1;
    PredicateAutomata::State state_counter = 0;
    for (unsigned level=1; level<=aut.qubitNum; level++) {
        for (PredicateAutomata::State i=0; i<pow_of_two; i++) {
            aut.transitions[Predicate(level)][state_counter].insert({(state_counter<<1)+1, (state_counter<<1)+2});
            state_counter++;
        }
        pow_of_two <<= 1;
    }
    for (PredicateAutomata::State i=state_counter; i<=(state_counter<<1); i++) {
        auto spf = states_probs.find(i-state_counter);
        if (spf == states_probs.end()) {
            if (default_prob == PredicateAutomata::Symbol())
                throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] The default amplitude is not specified!");
            aut.transitions[default_prob][i].insert({{}});
        }
        else
            aut.transitions[spf->second][i].insert({{}});
    }
    aut.finalStates.insert(0);
    aut.stateNum = (state_counter<<1) + 1;
    aut.reduce();

    return aut;
}

template <>
Automata<Concrete> TimbukParser<Concrete>::from_tree_to_automaton(std::string tree) {
    Automata<Concrete> aut;
    std::istringstream iss(tree);
    std::map<typename Automata<Concrete>::State, Concrete> states_probs;
    Complex::Complex default_prob;
    std::string state_prob;
    while (std::getline(iss, state_prob, '|')) {
        std::erase(state_prob, ' ');
        std::istringstream iss2(state_prob);
        std::string state;
        std::getline(iss2, state, ':');
        if (states_probs.empty()) {
            if (state == "*")
                throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] The numbers of qubits are not specified!");
            aut.qubitNum = state.length();
        } else if (state != "*" && aut.qubitNum != state.length())
            throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] The numbers of qubits are not the same in all basis states!");
        std::string t;
        if (state == "*") {
            std::getline(iss2, t);
            default_prob = ComplexParser(t).getComplex();
        } else {
            TreeAutomata::State s = std::stoll(state, nullptr, 2);
            std::getline(iss2, t);
            states_probs[s].complex = ComplexParser(t).getComplex();
        }
    }
    typename Automata<Concrete>::State pow_of_two = 1;
    typename Automata<Concrete>::State state_counter = 0;
    for (unsigned level=1; level<=aut.qubitNum; level++) {
        for (typename Automata<Concrete>::State i=0; i<pow_of_two; i++) {
            aut.transitions[Concrete(level)][state_counter].insert({(state_counter<<1)+1, (state_counter<<1)+2});
            state_counter++;
        }
        pow_of_two <<= 1;
    }
    for (typename Automata<Concrete>::State i=state_counter; i<=(state_counter<<1); i++) {
        auto spf = states_probs.find(i-state_counter);
        if (spf == states_probs.end()) {
            if (default_prob == Complex::Complex())
                throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] The default amplitude is not specified!");
            if (default_prob.size() == 5)
                aut.transitions[Concrete(default_prob)][i].insert({{}});
            else
                aut.transitions[Concrete(default_prob.at(0))][i].insert({{}});
        }
        else
            aut.transitions[spf->second][i].insert({{}});
    }
    aut.finalStates.insert(0);
    aut.stateNum = (state_counter<<1) + 1;
    aut.reduce();

    return aut;
}

template <>
Automata<Symbolic> TimbukParser<Symbolic>::from_tree_to_automaton(std::string tree) {
    Automata<Symbolic> aut;
    std::istringstream iss(tree);
    std::map<typename Automata<Symbolic>::State, Symbolic> states_probs;
    AUTOQ::Symbol::SymbolicComplex default_prob;
    std::string state_prob;
    while (std::getline(iss, state_prob, '|')) {
        std::erase(state_prob, ' ');
        std::istringstream iss2(state_prob);
        std::string state;
        std::getline(iss2, state, ':');
        if (states_probs.empty()) {
            if (state == "*")
                throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] The numbers of qubits are not specified!");
            aut.qubitNum = state.length();
        } else if (state != "*" && aut.qubitNum != state.length())
            throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] The numbers of qubits are not the same in all basis states!");
        std::string t;
        // } else if constexpr(std::is_same_v<Symbolic, SymbolicAutomata::Symbol>) {
        AUTOQ::Symbol::SymbolicComplex &symbolic_complex = std::invoke([&]()-> AUTOQ::Symbol::SymbolicComplex& {
            if (state == "*") {
                return default_prob;
            } else {
                SymbolicAutomata::State s = std::stoll(state, nullptr, 2);
                return states_probs[s].complex;
            }
        });
        std::getline(iss2, t);
        auto cp = ComplexParser(t);
        std::string var = cp.getVariable();
        if (var.length() > 0) // is a variable
            symbolic_complex[Complex::Complex::One()] = {{var, 1}};
        else // is a complex number
            symbolic_complex[cp.getComplex()] = {{"1", 1}};
    }
    typename Automata<Symbolic>::State pow_of_two = 1;
    typename Automata<Symbolic>::State state_counter = 0;
    for (unsigned level=1; level<=aut.qubitNum; level++) {
        for (typename Automata<Symbolic>::State i=0; i<pow_of_two; i++) {
            aut.transitions[Symbolic(level)][state_counter].insert({(state_counter<<1)+1, (state_counter<<1)+2});
            state_counter++;
        }
        pow_of_two <<= 1;
    }
    for (typename Automata<Symbolic>::State i=state_counter; i<=(state_counter<<1); i++) {
        auto spf = states_probs.find(i-state_counter);
        if (spf == states_probs.end()) {
            // if (default_prob == Symbolic())
            //     throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] The default amplitude is not specified!");
            aut.transitions[Symbolic(default_prob)][i].insert({{}});
        }
        else
            aut.transitions[spf->second][i].insert({{}});
    }
    aut.finalStates.insert(0);
    aut.stateNum = (state_counter<<1) + 1;
    aut.reduce();

    return aut;
}

template <typename Symbol>
Automata<Symbol> TimbukParser<Symbol>::from_line_to_automaton(std::string line) {
    std::istringstream iss_tensor(line);
    std::string tree;
    std::getline(iss_tensor, tree, '#');

    auto aut = from_tree_to_automaton(tree); // the first automata to be tensor producted

    // to tensor product with the rest of the automata
    while (std::getline(iss_tensor, tree, '#')) {
        auto aut2 = from_tree_to_automaton(tree);

        // let aut2 be tensor producted with aut here
        typename Automata<Symbol>::TransitionMap aut_leaves;
        for (const auto &t : aut.transitions) {
            if (t.first.is_leaf()) {
                aut_leaves[t.first] = t.second;
            }
        }
        for (const auto &t : aut_leaves) {
            aut.transitions.erase(t.first);
        }

        // append aut2 to each leaf transition of aut
        for (const auto &t : aut_leaves) {
            typename Automata<Symbol>::StateSet ss;
            for (const auto &out_ins : t.second) { // for (const auto &s2 : t.second.at({})) // simply apply these states
                // if (out_ins.second.contains({})) {
                    ss.insert(out_ins.first);
                // }
            }
            for (const auto &t2 : aut2.transitions) {
                if (t2.first.is_internal()) { // if the to-be-appended transition is internal, then
                    int Q = aut.qubitNum + t2.first.symbol().qubit(); // we need to shift the qubit number
                    for (const auto &kv : t2.second) { // for each pair of top -> ...
                        auto top = kv.first;
                        for (auto in : kv.second) { // ... -> set_vec_in
                            for (auto &e : in)
                                e += aut.stateNum;
                            // above shift the state number of vec_in first,
                            if (top == 0) { // if to be connected to leaf states of aut, then
                                for (const auto &s2 : ss) // simply apply these states
                                    aut.transitions[Symbol(Q)][s2].insert(in);
                            }
                            else // and then shift the state number of the top state
                                aut.transitions[Symbol(Q)][top + aut.stateNum].insert(in);
                        }
                    }
                } else {
                    for (const auto &kv : t2.second) {
                        auto top = kv.first;
                        for (auto in : kv.second) {
                            for (auto &e : in)
                                e += aut.stateNum;
                            aut.transitions[t.first.symbol() * t2.first.symbol()][top + aut.stateNum].insert(in);
                        }
                    }
                }
            }
            aut.stateNum += aut2.stateNum;
        }
        aut.qubitNum += aut2.qubitNum;
        aut.reduce();
    }
    return aut;
}

template <typename Symbol>
Automata<Symbol> TimbukParser<Symbol>::ReadAutomaton(const std::string& filepath) {
    std::string constraint;
    return ReadAutomatonAndConstraint(filepath, constraint);
}

template <typename Symbol>
AUTOQ::Automata<Symbol> TimbukParser<Symbol>::ReadAutomatonAndConstraint(const std::string& filepath, std::string& constraint) {
    std::ifstream file(filepath);
    std::string automaton;
    if (!file.is_open()) {
        std::cerr << "Error: Unable to open file." << std::endl;
        exit(1);
    }
    std::string fileContents((std::istreambuf_iterator<char>(file)), std::istreambuf_iterator<char>());
    file.close();
    size_t found = fileContents.find("Constraints");
    if (found != std::string::npos) {
        automaton = fileContents.substr(0, found);
        constraint = fileContents.substr(found + 11); // "Constraints".length()
    } else {
        automaton = fileContents;
        constraint = "";
    }
    if (boost::algorithm::ends_with(filepath, ".spec")) {
        return parse_automaton<Symbol>(automaton);
    } else if (boost::algorithm::ends_with(filepath, ".aut")) {
        return parse_timbuk<Symbol>(automaton);
    } else if (boost::algorithm::ends_with(filepath, ".hsl")) {
        return parse_hsl<Symbol>(automaton);
    } else {
        throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] The filename extension is not supported.");
    }
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>;
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>;