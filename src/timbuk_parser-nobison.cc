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
#include <autoq/parsing/timbuk_parser.hh>
#include <autoq/util/aut_description.hh>

using AUTOQ::Parsing::AbstrParser;
using AUTOQ::Parsing::TimbukParser;
using AUTOQ::Util::Predicate;
using AUTOQ::Util::Automata;
using AUTOQ::Util::TreeAutomata;
using AUTOQ::Util::SymbolicAutomata;
using AUTOQ::Util::PredicateAutomata;
using AUTOQ::Util::Convert;


/**
 * @brief  Trim whitespaces from a string (both left and right)
 */
static std::string trim(const std::string& str)
{
	std::string result = str;

	// trim from start
	result.erase(result.begin(), std::find_if(result.begin(), result.end(),
		[](int ch) {return !std::isspace(ch);}));

	// trim from end
	result.erase(std::find_if(result.rbegin(), result.rend(),
		[](int ch) {return !std::isspace(ch);}).base(), result.end());

	return result;
}


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
TreeAutomata::Symbol symbol_converter(const std::string& str)
{
	TreeAutomata::InitialSymbol temp;
    if (str[0] == '[') {
        for (int i=1; i<static_cast<int>(str.length()); i++) {
            size_t j = str.find(',', i);
            if (j == std::string::npos) j = str.length()-1;
            temp.push_back(boost::lexical_cast<TreeAutomata::InitialSymbol::Entry>(str.substr(i, j-i).c_str()));
            i = j;
        }
    } else {
        temp.push_back(boost::lexical_cast<TreeAutomata::InitialSymbol::Entry>(str.c_str()));
    }
    assert(temp.size() == 1 || temp.size() == 5);
    return temp;
}

SymbolicAutomata::Symbol symbol_converter2(const std::string& str)
{
	SymbolicAutomata::InitialSymbol temp;
    if (str[0] == '[') {
        for (int i=1; i<static_cast<int>(str.length()); i++) {
            size_t j = str.find(',', i);
            if (j == std::string::npos) j = str.length()-1;
            try {
                auto v = boost::lexical_cast<SymbolicAutomata::InitialSymbol::Entry>(str.substr(i, j-i).c_str());
                if (v == 0)
                    temp.push_back(AUTOQ::Util::Symbolic::Map());
                else
                    temp.push_back({{"1", v}});
            } catch (boost::bad_lexical_cast& e) {
                temp.push_back({{str.substr(i, j-i).c_str(), 1}});
            }
            i = j;
        }
    } else {
        try {
            auto v = boost::lexical_cast<SymbolicAutomata::InitialSymbol::Entry>(str.c_str());
            if (v == 0)
                temp.push_back(AUTOQ::Util::Symbolic::Map());
            else
                temp.push_back({{"1", v}});
        } catch (boost::bad_lexical_cast& e) {
            temp.push_back({{str.c_str(), 1}});
        }
    }
    assert(temp.size() == 1 || temp.size() == 5);
    return temp;
}

template <typename InitialSymbol>
static Automata<InitialSymbol> parse_timbuk(const std::string& str)
{
	Automata<InitialSymbol> result;

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
					throw std::runtime_error(std::string(__FUNCTION__) + "Automaton already parsed!");
				}

				aut_parsed = true;

				result.name = read_word(str);

				if (!str.empty())
				{
					throw std::runtime_error(std::string(__FUNCTION__) + ": line \"" + line +
						"\" has an unexpected string");
				}
			}
			else if ("Ops" == first_word)
			{
				// if (ops_parsed)
				// {
				// 	throw std::runtime_error(std::string(__FUNCTION__) + "Ops already parsed!");
				// }

				// ops_parsed = true;

				// while (!str.empty())
				// {
				// 	std::string label = read_word(str);
				// 	auto label_num = parse_colonned_token(label);
                //     auto temp = symbol_converter<InitialSymbol>(label_num.first);

				// 	// result.symbols[temp] = label_num.second;
				// }
			}
			else if ("States" == first_word)
			{
				if (states_parsed)
				{
					throw std::runtime_error(std::string(__FUNCTION__) + "States already parsed!");
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
					throw std::runtime_error(std::string(__FUNCTION__) + ": line \"" + line +
						"\" contains an unexpected string");
				}

				if (final_parsed)
				{
					throw std::runtime_error(std::string(__FUNCTION__) + "Final States already parsed!");
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
                    result.finalStates.push_back(t); //result.stateNum.TranslateFwd(state_num.first));
                    /****************************************************************************/
				}
			}
			else
			{	// guard
				throw std::runtime_error(std::string(__FUNCTION__) + ": line \"" + line +
					"\" contains an unexpected string");
			}
		}
		else
		{	// processing transitions
			std::string invalid_trans_str = std::string(__FUNCTION__) +
				": invalid transition \"" + line + "\"";

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
					(!std::is_same_v<InitialSymbol, PredicateAutomata::InitialSymbol> && contains_whitespace(lhs)) ||
					lhs.empty())
				{
					throw std::runtime_error(invalid_trans_str);
				}

				// result.transitions.insert(TreeAutomata::Transition({}, lhs, rhs));
                /*******************************************************************************************************************/
                int t = atoi(rhs.c_str());
                if (t > result.stateNum) result.stateNum = t;
                if constexpr(std::is_same_v<InitialSymbol, TreeAutomata::InitialSymbol>) {
                    auto temp = symbol_converter(lhs);
                    result.transitions[temp][std::vector<TreeAutomata::State>()].insert(t); //.stateNum.TranslateFwd(rhs));
                } else if constexpr(std::is_same_v<InitialSymbol, PredicateAutomata::InitialSymbol>) {
                    try {
                        result.transitions[Predicate(boost::multiprecision::cpp_int(lhs.substr(1, lhs.size()-2)))][std::vector<TreeAutomata::State>()].insert(t); //.stateNum.TranslateFwd(rhs));
                    } catch (...) {
                        result.transitions[Predicate(lhs.substr(1, lhs.size()-2).c_str())][std::vector<TreeAutomata::State>()].insert(t); //.stateNum.TranslateFwd(rhs));
                    }
                } else {
                    auto temp = symbol_converter2(lhs);
                    result.transitions[temp][std::vector<SymbolicAutomata::State>()].insert(t); //.stateNum.TranslateFwd(rhs));
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
                std::vector<typename Automata<InitialSymbol>::State> state_vector;
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
                if constexpr(std::is_same_v<InitialSymbol, TreeAutomata::InitialSymbol>) {
                    auto temp = symbol_converter(lab);
                    result.transitions[temp][state_vector].insert(t); //result.stateNum.TranslateFwd(rhs));
                } else if constexpr(std::is_same_v<InitialSymbol, PredicateAutomata::InitialSymbol>) {
                    try {
                        result.transitions[Predicate(boost::multiprecision::cpp_int(lab.substr(1, lab.size()-2)))][state_vector].insert(t); //.stateNum.TranslateFwd(rhs));
                    } catch (...) {
                        result.transitions[Predicate(lab.substr(1, lab.size()-2).c_str())][state_vector].insert(t); //result.stateNum.TranslateFwd(rhs));
                    }
                } else {
                    auto temp = symbol_converter2(lab);
                    result.transitions[temp][state_vector].insert(t); //result.stateNum.TranslateFwd(rhs));
                }
                /*********************************************************************************************/
			}
		}
	}

	if (!are_transitions)
	{
		throw std::runtime_error(std::string(__FUNCTION__) + ": Transitions not specified");
	}

    for (const auto &kv : result.transitions) {
        if (kv.first.is_internal()) {
            if (kv.first.initial_symbol().qubit() > INT_MAX)
                throw std::overflow_error("");
            result.qubitNum = std::max(result.qubitNum, static_cast<int>(kv.first.initial_symbol().qubit()));
        }
    }
    result.stateNum++;
	return result;
}

template <typename InitialSymbol>
Automata<InitialSymbol> TimbukParser<InitialSymbol>::ParseString(const std::string& str)
{
	Automata<InitialSymbol> timbukParse;

	try
	{
		timbukParse = parse_timbuk<InitialSymbol>(str);
	}
	catch (std::exception& ex)
	{
		throw std::runtime_error("Error: \'" + std::string(ex.what()) +
			"\' while parsing \n" + str);
	}

	return timbukParse;
}

template <typename InitialSymbol>
Automata<InitialSymbol> TimbukParser<InitialSymbol>::FromFileToAutomata(const char* filepath)
{
    std::ifstream t(filepath);
    std::stringstream buffer;
    buffer << t.rdbuf();
    return ParseString(buffer.str());
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Util::Concrete>;
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Util::Symbolic>;
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Util::Predicate>;