/*****************************************************************************
 *  AUTOQ Timbuk parser – transition table (.lsta-style).
 *
 *  Parses Root States + Transitions. Every label is [symbol,color].
 *  Depends on timbuk_parser_grammar.hh for parse_symbol.
 *
 *  Main function: parse_automaton(str, constants, predicates, ...).
 *****************************************************************************/
#ifndef AUTOQ_PARSING_TIMBUK_PARSER_TRANSITIONS_HH
#define AUTOQ_PARSING_TIMBUK_PARSER_TRANSITIONS_HH
#include <algorithm>
#include <cctype>
#include <regex>
#include <boost/multiprecision/cpp_int.hpp>
#include "autoq/error.hh"
#include "autoq/error_messages.hh"
#include "autoq/parsing/parser/timbuk_parser_grammar.hh"
#include "autoq/parsing/parser/timbuk_parser_util.hh"

namespace {
const std::regex kRootStates("Root +States");

// A colored label is "symbol,color". The color is checked before the symbol
// is parsed, so a missing or non-numeric color is an invalid transition and
// is not mistaken for an undefined constant (#36).
template <typename Tag>
std::pair<std::string, Tag> split_colored_label(const std::string& label, const std::string& invalid_trans_str) {
    const auto comma = label.find(',');
    if (comma == std::string::npos)
        THROW_AUTOQ_ERROR(invalid_trans_str);
    const std::string symbol = AUTOQ::String::trim(label.substr(0, comma));
    const std::string color_text = AUTOQ::String::trim(label.substr(comma + 1));
    const bool numeric = !color_text.empty() &&
        std::all_of(color_text.begin(), color_text.end(), [](unsigned char c) { return std::isdigit(c) != 0; });
    if (symbol.empty() || !numeric || color_text.find(',') != std::string::npos)
        THROW_AUTOQ_ERROR(invalid_trans_str);
    try {
        return {symbol, boost::lexical_cast<Tag>(color_text)};
    } catch (const boost::bad_lexical_cast&) {
        THROW_AUTOQ_ERROR(invalid_trans_str);
    }
}

// Colors into one state are bitsets and must be pairwise disjoint (#54).
template <typename Symbol>
void require_disjoint_color(const AUTOQ::Automata<Symbol>& aut,
                            typename AUTOQ::Automata<Symbol>::State state,
                            typename AUTOQ::Automata<Symbol>::Tag color,
                            const std::string& state_name,
                            const std::string& transition) {
    for (const auto& kv : aut.transitions) {
        if ((kv.first.tag() & color) == 0)
            continue;
        if (kv.second.find(state) == kv.second.end())
            continue;
        THROW_AUTOQ_ERROR("The colors of transitions into state \"" + state_name +
                          "\" are not disjoint in \"" + transition + "\".");
    }
}

// A leaf has no child tuple, so a numeric symbol is an amplitude, not a qubit (#30).
bool is_integer_literal(const std::string& token) {
    if (token.empty())
        return false;
    const size_t first_digit = (token[0] == '+' || token[0] == '-') ? 1 : 0;
    if (first_digit == token.size())
        return false;
    return std::all_of(token.begin() + static_cast<std::ptrdiff_t>(first_digit), token.end(),
                        [](unsigned char c) { return std::isdigit(c) != 0; });
}
}

template <typename Symbol>
AUTOQ::Automata<Symbol> parse_automaton(const std::string& str, const std::map<std::string, AUTOQ::Complex::Complex> &constants, const std::map<std::string, std::string> &predicates, bool throw_on_undefined, bool* out_encountered_undefined) {
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
            }
            std::smatch root_header;
            if (std::regex_search(str, root_header, kRootStates)) {  // processing root states
                // The header words are not state names. "Root States q" names only q (#31).
                str = AUTOQ::String::trim(root_header.suffix().str());
                while (!str.empty()) {
                    std::string state = AUTOQ::String::read_word(str);
                    auto state_num = AUTOQ::String::parse_colonned_token(state);
                    result_finalStates.insert(state_num.first);
                }
                already_root_states = true;
                continue;
            }
            if (str == "Transitions") {
                if (!already_root_states) {
                    THROW_AUTOQ_ERROR(AUTOQ::ErrorMessages::kRootStatesNotSpecified);
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
                if (lhs.size() < 2 || lhs.front() != '[' || lhs.back() != ']')
                    THROW_AUTOQ_ERROR(invalid_trans_str);
                lhs = lhs.substr(1, lhs.size()-2);
                int t;
                auto it = states.find(rhs);
                if (it == states.end()) {
                    t = states.size();
                    states[rhs] = t;
                } else
                    t = it->second; //atoi(rhs.c_str());
                if (t > result.stateNum) result.stateNum = t;
                if constexpr(std::is_same_v<Symbol, AUTOQ::ConcreteAutomata::Symbol>) {
                    try {
                        auto [token, color] = split_colored_label<AUTOQ::ConcreteAutomata::Tag>(lhs, invalid_trans_str);
                        if (is_integer_literal(token)) {
                            // No children: the number is an amplitude. Symbol(int) would build a qubit.
                            auto value = AUTOQ::Complex::Complex(boost::multiprecision::cpp_int(token));
                            AUTOQ::Parsing::align_leaf_to_constants(value, constants);
                            auto sym = Symbol(value);
                            require_disjoint_color<Symbol>(result, t, color, rhs, str);
                            result.transitions[AUTOQ::ConcreteAutomata::SymbolTag(sym, AUTOQ::ConcreteAutomata::Tag(color))][t].insert(std::vector<AUTOQ::ConcreteAutomata::State>());
                        } else {
                            auto it = constants.find(token);
                            if (it == constants.end()) {
                                if (!throw_on_undefined) {
                                    if (out_encountered_undefined) *out_encountered_undefined = true;
                                    return {};
                                }
                                THROW_AUTOQ_ERROR(std::string(AUTOQ::ErrorMessages::kConstantNotDefinedPrefix) + token + AUTOQ::ErrorMessages::kConstantNotDefinedSuffix);
                            }
                            auto sym = Symbol(it->second);
                            require_disjoint_color<Symbol>(result, t, color, rhs, str);
                            result.transitions[AUTOQ::ConcreteAutomata::SymbolTag(sym, AUTOQ::ConcreteAutomata::Tag(color))][t].insert(std::vector<AUTOQ::ConcreteAutomata::State>());
                        }
                    } catch (const AutoQError&) {
                        throw;
                    } catch (...) {
                        THROW_AUTOQ_ERROR(invalid_trans_str);
                    }
                } else if constexpr(std::is_same_v<Symbol, AUTOQ::PredicateAutomata::Symbol>) {
                    try {
                        auto [token, color] = split_colored_label<AUTOQ::PredicateAutomata::Tag>(lhs, invalid_trans_str);
                        // No children: a number is not a qubit. Look the leaf up as a predicate.
                        auto it = predicates.find(token);
                        if (it == predicates.end()) {
                            if (!throw_on_undefined) {
                                if (out_encountered_undefined) *out_encountered_undefined = true;
                                return {};
                            }
                            THROW_AUTOQ_ERROR(std::string(AUTOQ::ErrorMessages::kConstantNotDefinedPrefix) + token + AUTOQ::ErrorMessages::kConstantNotDefinedSuffix);
                        }
                        auto sym = Symbol(it->second.c_str());
                        require_disjoint_color<Symbol>(result, t, color, rhs, str);
                        result.transitions[AUTOQ::PredicateAutomata::SymbolTag(sym, AUTOQ::PredicateAutomata::Tag(color))][t].insert(std::vector<AUTOQ::PredicateAutomata::State>());
                    } catch (const AutoQError&) {
                        throw;
                    } catch (...) {
                        THROW_AUTOQ_ERROR(invalid_trans_str);
                    }
                } else { // if constexpr(std::is_same_v<Symbol, AUTOQ::SymbolicAutomata::Symbol>) {
                    auto [token, color] = split_colored_label<AUTOQ::SymbolicAutomata::Tag>(lhs, invalid_trans_str);
                    EvaluationVisitor<>::SymbolicComplexParser scp(token, constants);
                    auto sym = Symbol(scp.getSymbolicComplex());
                    require_disjoint_color<Symbol>(result, t, color, rhs, str);
                    result.transitions[AUTOQ::SymbolicAutomata::SymbolTag(sym, AUTOQ::SymbolicAutomata::Tag(color))][t].insert(std::vector<AUTOQ::SymbolicAutomata::State>());
                    for (const auto &var: scp.getNewVars())
                        result.vars.insert(var);
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
                if (symbol.size() < 2 || symbol.front() != '[' || symbol.back() != ']')
                    THROW_AUTOQ_ERROR(invalid_trans_str);
                symbol = symbol.substr(1, symbol.length()-2);
                if constexpr(std::is_same_v<Symbol, AUTOQ::ConcreteAutomata::Symbol>) {
                    auto [token, color] = split_colored_label<AUTOQ::ConcreteAutomata::Tag>(symbol, invalid_trans_str);
                    try {
                        auto sym = Symbol(boost::lexical_cast<int>(token));
                        require_disjoint_color<Symbol>(result, t, color, rhs, str);
                        result.transitions[AUTOQ::ConcreteAutomata::SymbolTag(sym, AUTOQ::ConcreteAutomata::Tag(color))][t].insert(state_vector);
                    } catch (const AutoQError&) {
                        throw;
                    } catch (...) {
                        THROW_AUTOQ_ERROR(invalid_trans_str);
                    }
                    // if (boost::lexical_cast<int>(symbol) == 1)
                    //     result.finalStates.push_back(t);
                } else if constexpr(std::is_same_v<Symbol, AUTOQ::PredicateAutomata::Symbol>) {
                    auto [token, color] = split_colored_label<AUTOQ::PredicateAutomata::Tag>(symbol, invalid_trans_str);
                    auto sym = parse_symbol<Symbol>(token);
                    require_disjoint_color<Symbol>(result, t, color, rhs, str);
                    result.transitions[AUTOQ::PredicateAutomata::SymbolTag(sym, AUTOQ::PredicateAutomata::Tag(color))][t].insert(state_vector);
                    // if (boost::lexical_cast<int>(sym.qubit()) == 1)
                    //     result.finalStates.push_back(t);
                } else { // if constexpr(std::is_same_v<Symbol, AUTOQ::SymbolicAutomata::Symbol>) {
                    auto [token, color] = split_colored_label<AUTOQ::SymbolicAutomata::Tag>(symbol, invalid_trans_str);
                    auto sym = parse_symbol<Symbol>(token);
                    require_disjoint_color<Symbol>(result, t, color, rhs, str);
                    result.transitions[AUTOQ::SymbolicAutomata::SymbolTag(sym, AUTOQ::SymbolicAutomata::Tag(color))][t].insert(state_vector);
                    // if (boost::lexical_cast<int>(sym.qubit()) == 1)
                    //     result.finalStates.push_back(t);
                }
                /*********************************************************************************************/
			}
		}
	}

	if (!start_transitions) {
		THROW_AUTOQ_ERROR(AUTOQ::ErrorMessages::kTransitionsNotSpecified);
	}

    for (const auto &kv : result.transitions) {
        if (kv.first.is_internal()) {
            if (kv.first.symbol().qubit() > INT_MAX)
                THROW_AUTOQ_ERROR(AUTOQ::ErrorMessages::kQubitNumTooLarge);
            result.qubitNum = std::max(result.qubitNum, static_cast<int>(kv.first.symbol().qubit()));
        }
    }

    for (const auto &s : result_finalStates) {
        auto it = states.find(s);
        if (it == states.end())
            THROW_AUTOQ_ERROR("Root state \"" + s + "\" does not occur in any transition.");
        result.finalStates.push_back(it->second);
    }
    result.stateNum++; // because the state number starts from 0
	return result;
}

#endif
