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
#include <autoq/parsing/timbuk_parser.hh>
#include <autoq/util/aut_description.hh>
#include <boost/algorithm/string/predicate.hpp>

using AUTOQ::Parsing::AbstrParser;
using AUTOQ::Parsing::TimbukParser;
using AUTOQ::Util::Predicate;
using AUTOQ::Util::Automata;
using AUTOQ::Util::TreeAutomata;
using AUTOQ::Util::SymbolicAutomata;
using AUTOQ::Util::PredicateAutomata;
using AUTOQ::Util::Convert;
using AUTOQ::Util::trim;

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
TreeAutomata::InitialSymbol from_string_to_Concrete(const std::string& str)
{
	TreeAutomata::InitialSymbol temp;
    if (str[0] == '[') {
        for (int i=1; i<static_cast<int>(str.length()); i++) {
            size_t j = str.find(',', i);
            if (j == std::string::npos) j = str.length()-1;
            try {
                temp.push_back(boost::lexical_cast<TreeAutomata::InitialSymbol::Entry>(str.substr(i, j-i).c_str()));
            } catch (...) {
                throw std::runtime_error("[ERROR] The input entry \"" + str.substr(i, j-i) + "\" is not an integer!");
            }
            i = j;
        }
    } else {
        try {
            temp.push_back(boost::lexical_cast<TreeAutomata::InitialSymbol::Entry>(str.c_str()));
        } catch (...) {
            throw std::runtime_error("[ERROR] The input entry \"" + str + "\" is not an integer!");
        }
    }
    assert(temp.size() == 1 || temp.size() == 5);
    return temp;
}

SymbolicAutomata::InitialSymbol from_string_to_Symbolic(const std::string& str)
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

PredicateAutomata::InitialSymbol from_string_to_Predicate(const std::string& lhs)
{
    try {
        return Predicate(boost::multiprecision::cpp_int(lhs.substr(1, lhs.size()-2)));
    } catch (...) {
        return Predicate(lhs.substr(1, lhs.size()-2).c_str());
    }
}

template <typename InitialSymbol>
Automata<InitialSymbol> parse_timbuk(const std::string& str)
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
					throw std::runtime_error(std::string(__FUNCTION__) + ": Automaton already parsed!");
				}

				aut_parsed = true;

				result.name = read_word(str);

				if (!str.empty())
				{
					throw std::runtime_error(std::string(__FUNCTION__) + ": Line \"" + line +
						"\" has an unexpected string.");
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
					throw std::runtime_error(std::string(__FUNCTION__) + ": States already parsed!");
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
					throw std::runtime_error(std::string(__FUNCTION__) + ": Line \"" + line +
						"\" contains an unexpected string.");
				}

				if (final_parsed)
				{
					throw std::runtime_error(std::string(__FUNCTION__) + ": Final States already parsed!");
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
				throw std::runtime_error(std::string(__FUNCTION__) + ": Line \"" + line +
					"\" contains an unexpected string.");
			}
		}
		else
		{	// processing transitions
			std::string invalid_trans_str = std::string(__FUNCTION__) +
				": Invalid transition \"" + line + "\".";

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
                    auto temp = from_string_to_Concrete(lhs);
                    result.transitions[temp][std::vector<TreeAutomata::State>()].insert(t); //.stateNum.TranslateFwd(rhs));
                } else if constexpr(std::is_same_v<InitialSymbol, PredicateAutomata::InitialSymbol>) {
                    auto temp = from_string_to_Predicate(lhs);
                    result.transitions[temp][std::vector<TreeAutomata::State>()].insert(t); //.stateNum.TranslateFwd(rhs));
                } else {
                    auto temp = from_string_to_Symbolic(lhs);
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
                    auto temp = from_string_to_Concrete(lab);
                    result.transitions[temp][state_vector].insert(t); //result.stateNum.TranslateFwd(rhs));
                } else if constexpr(std::is_same_v<InitialSymbol, PredicateAutomata::InitialSymbol>) {
                    auto temp = from_string_to_Predicate(lab);
                    result.transitions[temp][state_vector].insert(t); //.stateNum.TranslateFwd(rhs));
                } else {
                    auto temp = from_string_to_Symbolic(lab);
                    result.transitions[temp][state_vector].insert(t); //result.stateNum.TranslateFwd(rhs));
                }
                /*********************************************************************************************/
			}
		}
	}

	if (!are_transitions)
	{
		throw std::runtime_error(std::string(__FUNCTION__) + ": Transitions not specified.");
	}

    boost::multiprecision::cpp_int k = -1;
    for (const auto &kv : result.transitions) {
        if (kv.first.is_internal()) {
            if (kv.first.initial_symbol().qubit() > INT_MAX)
                throw std::overflow_error("[ERROR] The number of qubits is too large!");
            result.qubitNum = std::max(result.qubitNum, static_cast<int>(kv.first.initial_symbol().qubit()));
        } else { // leaf transitions
            if (k == -1) {
                k = kv.first.initial_symbol().k();
                if (k < 0)
                    throw std::runtime_error("[ERROR] The k value cannot be less than 0.");
            }
            else if (k != kv.first.initial_symbol().k()) {
                throw std::runtime_error("[ERROR] All k's in the automaton must be the same!");
            }
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
		throw std::runtime_error("[ERROR] \'" + std::string(ex.what()) +
			"\'\nwhile parsing the following automaton.\n\n>>>>>>>>>>>>>>>>>>>>\n" + str + "\n<<<<<<<<<<<<<<<<<<<<");
	}

	return timbukParse;
}

template <> // The loop reading part is different from other types, so we have to specialize this type.
PredicateAutomata TimbukParser<Predicate>::from_tree_to_automaton(std::string tree) {
    PredicateAutomata aut;
    std::map<PredicateAutomata::State, PredicateAutomata::InitialSymbol> states_probs;
    PredicateAutomata::InitialSymbol default_prob;
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
    for (int level=1; level<=aut.qubitNum; level++) {
        for (PredicateAutomata::State i=0; i<pow_of_two; i++) {
            aut.transitions[Predicate(level)][{(state_counter<<1)+1, (state_counter<<1)+2}] = {state_counter};
            state_counter++;
        }
        pow_of_two <<= 1;
    }
    for (PredicateAutomata::State i=state_counter; i<=(state_counter<<1); i++) {
        auto spf = states_probs.find(i-state_counter);
        if (spf == states_probs.end()) {
            if (default_prob == PredicateAutomata::InitialSymbol())
                throw std::runtime_error("[ERROR] The default amplitude is not specified!");
            aut.transitions[default_prob][{}].insert(i);
        }
        else
            aut.transitions[spf->second][{}].insert(i);
    }
    aut.finalStates.push_back(0);
    aut.stateNum = (state_counter<<1) + 1;
    aut.reduce();

    return aut;
}

template <typename InitialSymbol>
Automata<InitialSymbol> TimbukParser<InitialSymbol>::from_tree_to_automaton(std::string tree) {
    Automata<InitialSymbol> aut;
    std::istringstream iss(tree);
    std::map<typename Automata<InitialSymbol>::State, InitialSymbol> states_probs;
    InitialSymbol default_prob;
    boost::multiprecision::cpp_int k = -1;
    for (std::string state_prob; iss >> state_prob;) {
        std::istringstream iss2(state_prob);
        std::string state;
        std::getline(iss2, state, ':');
        if (states_probs.empty())
            aut.qubitNum = state.length();
        else if (aut.qubitNum != state.length())
            throw std::runtime_error("[ERROR] The numbers of qubits are not the same in all basis states!");
        std::string t;
        if constexpr(std::is_same_v<InitialSymbol, TreeAutomata::InitialSymbol>) {
            if (state == "*") {
                while (std::getline(iss2, t, ',')) {
                    try {
                        default_prob.push_back(boost::lexical_cast<TreeAutomata::InitialSymbol::Entry>(t.c_str()));
                    } catch (...) {
                        throw std::runtime_error("[ERROR] The input entry \"" + t + "\" is not an integer!");
                    }
                }
                if (k == -1) {
                    k = default_prob.k();
                    if (k < 0)
                        throw std::runtime_error("[ERROR] The k value cannot be less than 0.");
                }
                else if (k != default_prob.k()) {
                    throw std::runtime_error("[ERROR] All k's in the automaton must be the same!");
                }
            } else {
                TreeAutomata::State s = std::stoll(state, nullptr, 2);
                auto &sps = states_probs[s];
                while (std::getline(iss2, t, ',')) {
                    try {
                        sps.push_back(boost::lexical_cast<TreeAutomata::InitialSymbol::Entry>(t.c_str()));
                    } catch (...) {
                        throw std::runtime_error("[ERROR] The input entry \"" + t + "\" is not an integer!");
                    }
                }
                if (k == -1) {
                    k = sps.k();
                    if (k < 0)
                        throw std::runtime_error("[ERROR] The k value cannot be less than 0.");
                }
                else if (k != sps.k()) {
                    throw std::runtime_error("[ERROR] All k's in the automaton must be the same!");
                }
            }
        } else if constexpr(std::is_same_v<InitialSymbol, SymbolicAutomata::InitialSymbol>) {
            if (state == "*") {
                while (std::getline(iss2, t, ',')) {
                    try {
                        auto v = boost::lexical_cast<SymbolicAutomata::InitialSymbol::Entry>(t.c_str());
                        if (v == 0)
                            default_prob.push_back(AUTOQ::Util::Symbolic::Map());
                        else
                            default_prob.push_back({{"1", v}});
                    } catch (boost::bad_lexical_cast& e) {
                        default_prob.push_back({{t.c_str(), 1}});
                    }
                }
                if (k == -1) {
                    k = default_prob.k();
                    if (k < 0)
                        throw std::runtime_error("[ERROR] The k value cannot be less than 0.");
                }
                else if (k != default_prob.k()) {
                    throw std::runtime_error("[ERROR] All k's in the automaton must be the same!");
                }
            } else {
                SymbolicAutomata::State s = std::stoll(state, nullptr, 2);
                auto &sps = states_probs[s];
                while (std::getline(iss2, t, ',')) {
                    try {
                        auto v = boost::lexical_cast<SymbolicAutomata::InitialSymbol::Entry>(t.c_str());
                        if (v == 0)
                            sps.push_back(AUTOQ::Util::Symbolic::Map());
                        else
                            sps.push_back({{"1", v}});
                    } catch (boost::bad_lexical_cast& e) {
                        sps.push_back({{t.c_str(), 1}});
                    }
                }
                if (k == -1) {
                    k = sps.k();
                    if (k < 0)
                        throw std::runtime_error("[ERROR] The k value cannot be less than 0.");
                }
                else if (k != sps.k()) {
                    throw std::runtime_error("[ERROR] All k's in the automaton must be the same!");
                }
            }
        } else {
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
    }
    typename Automata<InitialSymbol>::State pow_of_two = 1;
    typename Automata<InitialSymbol>::State state_counter = 0;
    for (int level=1; level<=aut.qubitNum; level++) {
        for (typename Automata<InitialSymbol>::State i=0; i<pow_of_two; i++) {
            aut.transitions[InitialSymbol(level)][{(state_counter<<1)+1, (state_counter<<1)+2}] = {state_counter};
            state_counter++;
        }
        pow_of_two <<= 1;
    }
    for (typename Automata<InitialSymbol>::State i=state_counter; i<=(state_counter<<1); i++) {
        auto spf = states_probs.find(i-state_counter);
        if (spf == states_probs.end()) {
            if (default_prob == InitialSymbol())
                throw std::runtime_error("[ERROR] The default amplitude is not specified!");
            aut.transitions[default_prob][{}].insert(i);
        }
        else
            aut.transitions[spf->second][{}].insert(i);
    }
    aut.finalStates.push_back(0);
    aut.stateNum = (state_counter<<1) + 1;
    aut.reduce();

    return aut;
}

template <typename InitialSymbol>
Automata<InitialSymbol> TimbukParser<InitialSymbol>::from_line_to_automaton(std::string line) {
    std::istringstream iss_tensor(line);
    std::string tree;
    std::getline(iss_tensor, tree, '#');

    auto aut = from_tree_to_automaton(tree); // the first automata to be tensor producted

    // to tensor product with the rest of the automata
    while (std::getline(iss_tensor, tree, '#')) {
        auto aut2 = from_tree_to_automaton(tree);

        // let aut2 be tensor producted with aut here
        typename Automata<InitialSymbol>::TransitionMap aut_leaves;
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
            for (const auto &t2 : aut2.transitions) {
                if (t2.first.is_internal()) { // if the to-be-appended transition is internal, then
                    auto Q = aut.qubitNum + t2.first.initial_symbol().qubit(); // we need to shift the qubit number
                    for (const auto &kv : t2.second) { // for each pair of vec_in -> set_out
                        auto k = kv.first;
                        for (int i=0; i<k.size(); i++)
                            k.at(i) += aut.stateNum;
                        // above shift the state number of vec_in first,
                        for (const auto &s : kv.second) {
                            if (s == 0) { // if to be connected to leaf states of aut, then
                                for (const auto &s2 : t.second.at({})) // simply apply these states
                                    aut.transitions[{Q}][k].insert(s2);
                            }
                            else // and then shift the state number of set_out
                                aut.transitions[{Q}][k].insert(s + aut.stateNum);
                        }
                    }
                } else {
                    for (const auto &kv : t2.second) {
                        auto k = kv.first;
                        for (int i=0; i<k.size(); i++)
                            k.at(i) += aut.stateNum;
                        for (const auto &s : kv.second) {
                            aut.transitions[t.first.initial_symbol() * t2.first.initial_symbol()][k].insert(s + aut.stateNum);
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

template <typename InitialSymbol>
Automata<InitialSymbol> TimbukParser<InitialSymbol>::FromFileToAutomata(const char* filepath)
{
    if (boost::algorithm::ends_with(filepath, ".aut")) {
        std::ifstream t(filepath);
        if (!t) // in case the file could not be open
            throw std::runtime_error("[ERROR] Failed to open file " + std::string(filepath) + ".");
        std::stringstream buffer;
        buffer << t.rdbuf();
        return ParseString(buffer.str());
    } else if (boost::algorithm::ends_with(filepath, ".hsl")) {
        Automata<InitialSymbol> aut_final;
        std::string line;
        std::ifstream file(filepath);
        if (!file) // in case the file could not be open
            throw std::runtime_error("[ERROR] Failed to open file " + std::string(filepath) + ".");
        while (std::getline(file, line)) {
            line = AUTOQ::Util::trim(line);
            if (line.substr(0, 4) == "|i|=") { // if startswith "|i|="
                std::istringstream iss(line);
                std::string length; iss >> length; length = length.substr(4);
                line.clear();
                for (std::string t; iss >> t;)
                    line += t + ' ';
                std::string i(std::atoi(length.c_str()), '1');
                bool reach_all_zero;
                do {
                    auto aut = from_line_to_automaton(std::regex_replace(line, std::regex("i:"), i + ":"));
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
                auto aut = from_line_to_automaton(line);
                aut_final = aut_final.Union(aut);
                aut_final.reduce();
            }
        }
        // DO NOT fraction_simplification() here since the resulting automaton may be used as pre.aut
        // and in this case all k's must be the same.
        return aut_final;
    } else {
        throw std::runtime_error("[ERROR] " + std::string(__FUNCTION__) + ": The filename extension is not supported.");
    }
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Util::Concrete>;
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Util::Symbolic>;
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Util::Predicate>;