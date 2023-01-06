/*****************************************************************************
 *  VATA Tree Automata Library
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

// VATA headers
#include <vata/vata.hh>
#include <vata/parsing/timbuk_parser.hh>
#include <vata/util/aut_description.hh>

using VATA::Parsing::AbstrParser;
using VATA::Parsing::TimbukParser;
using VATA::Util::TreeAutomata;
using VATA::Util::Convert;


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
            temp.push_back(boost::lexical_cast<TreeAutomata::SymbolEntry>(str.substr(i, j-i).c_str()));
            i = j;
        }
    } else {
        temp.push_back(boost::lexical_cast<TreeAutomata::SymbolEntry>(str.c_str()));
    }
    assert(temp.size() == 1 || temp.size() == 5);
    return temp;
}
static TreeAutomata parse_timbuk(const std::string& str)
{
	TreeAutomata result;

	bool are_transitions = false;
	bool aut_parsed = false;
	bool ops_parsed = false;
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
				if (ops_parsed)
				{
					throw std::runtime_error(std::string(__FUNCTION__) + "Ops already parsed!");
				}

				ops_parsed = true;

				while (!str.empty())
				{
					std::string label = read_word(str);
					auto label_num = parse_colonned_token(label);
                    auto temp = symbol_converter(label_num.first);

					// result.symbols[temp] = label_num.second;
				}
			}
			else if ("States" == first_word)
			{
				if (states_parsed)
				{
					throw std::runtime_error(std::string(__FUNCTION__) + "States already parsed!");
				}

				states_parsed = true;

				while (!str.empty())
				{
					std::string state = read_word(str);
					auto state_num = parse_colonned_token(state);
					// result.states.insert(state_num.first);
                    /****************************************************************************************/
                    // assert(result.stateNum.FindFwd(state_num.first) == result.stateNum.end());
                    result.stateNum++; //.insert(std::make_pair(state_num.first, result.stateNum.size()));
                    /****************************************************************************************/
				}
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
                    result.finalStates.push_back(atoi(state_num.first.c_str())); //result.stateNum.TranslateFwd(state_num.first));
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
			if (std::string::npos == parens_begin_pos)
			{	// no tuple of states
				if ((std::string::npos != parens_end_pos) ||
					contains_whitespace(lhs) ||
					lhs.empty())
				{
					throw std::runtime_error(invalid_trans_str);
				}

				// result.transitions.insert(TreeAutomata::Transition({}, lhs, rhs));
                /*******************************************************************************************************************/
                auto temp = symbol_converter(lhs);
                result.transitions[temp][std::vector<TreeAutomata::State>()].insert(atoi(rhs.c_str())); //.stateNum.TranslateFwd(rhs));
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
                std::vector<TreeAutomata::State> state_vector;
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
                    if (state.length() > 0)
                        state_vector.push_back(atoi(state.c_str())); //.stateNum.TranslateFwd(state));
                    /*******************************************************************/
				}

				if ((state_tuple.size() == 1) && state_tuple[0] == "")
				{
					state_tuple = { };
				}

				// result.transitions.insert(TreeAutomata::Transition(state_tuple, lab, rhs));
                /*********************************************************************************************/
                auto temp = symbol_converter(lab);
                result.transitions[temp][state_vector].insert(atoi(rhs.c_str())); //result.stateNum.TranslateFwd(rhs));
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

	return result;
}

TreeAutomata TimbukParser::ParseString(const std::string& str)
{
	TreeAutomata timbukParse;

	try
	{
		timbukParse = parse_timbuk(str);
	}
	catch (std::exception& ex)
	{
		throw std::runtime_error("Error: \'" + std::string(ex.what()) +
			"\' while parsing \n" + str);
	}

	return timbukParse;
}

TreeAutomata TimbukParser::FromFileToAutomata(const char* filepath)
{
    std::ifstream t(filepath);
    std::stringstream buffer;
    buffer << t.rdbuf();
    return ParseString(buffer.str());
}