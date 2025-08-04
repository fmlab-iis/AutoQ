/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Copyright (c) 2011  Ondra Lengal <ilengal@fit.vutbr.cz>
 *
 *  Description:
 *    Implementation file for a serializer of automata to Timbuk format.
 *
 *****************************************************************************/

// AUTOQ headers
#include <regex>
#include "autoq/error.hh"
#include "autoq/aut_description.hh"
#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/symbol/predicate.hh"
#include "autoq/serialization/timbuk_serializer.hh"

using AUTOQ::Util::Convert;
using AUTOQ::Automata;
using AUTOQ::TreeAutomata;
using AUTOQ::SymbolicAutomata;
using AUTOQ::PredicateAutomata;
using AUTOQ::Serialization::TimbukSerializer;

// Standard library headers
#include <algorithm>

using std::for_each;

template <typename Symbol>
std::string TimbukSerializer::Serialize(Automata<Symbol> desc)
{
    if constexpr(!std::is_same_v<Symbol, AUTOQ::Symbol::Predicate>
              && !std::is_same_v<Symbol, AUTOQ::Symbol::Index>) {
        desc.fraction_simplification();
    }

	std::string result;
	// result += "Ops ";
	// for (auto itSymb = desc.transitions.cbegin();
	// 	itSymb != desc.transitions.cend(); ++itSymb)
	// {
    //     if (std::is_convertible<Symbol, std::string>::value)
    //         result += "[" + AUTOQ::Util::Convert::ToString(itSymb->first) + "]:" +
	// 		    AUTOQ::Util::Convert::ToString(itSymb->second.begin()->second.begin()->size()) + " ";
    //     else
	// 	    result += AUTOQ::Util::Convert::ToString(itSymb->first) + ":" +
	// 		    AUTOQ::Util::Convert::ToString(itSymb->second.begin()->second.begin()->size()) + " ";
	// }

	// result += "\n";
	// result += "Automaton " + (desc.name.empty()? "anonymous" : desc.name);

	// result += "\n";
	// result += "States ";
    // for (auto i=0; i<desc.stateNum; i++) {
    //     result += std::to_string(i) + " ";
    //     // result += desc.stateNum.TranslateBwd(i) + " ";
    // }
	// for_each(desc.states.cbegin(), desc.states.cend(),
	// 	[&result](const std::string& sStr){ result += sStr + " ";});

    if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Concrete>)
        result += "Constants\n";
    else if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Symbolic>)
        result += "Expressions\n";
    else if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Predicate>)
        result += "Predicates\n";
    else
        THROW_AUTOQ_ERROR("This kind of symbol is still unsupported!");
    std::map<Symbol, size_t> leafMap;
    for (const auto &t : desc.transitions) {
        if (t.first.is_leaf()) {
            const auto &sym = t.first.symbol();
            auto it = leafMap.find(sym);
            if (it == leafMap.end()) {
                if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Concrete>)
                    result += "c" + std::to_string(leafMap.size()) + " := " + Convert::ToString(sym) + "\n";
                else if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Symbolic>) {
                    auto str = Convert::ToString(sym);
                    str = std::regex_replace(str, std::regex(R"(([^ ]+)R)"), "real($1)");
                    str = std::regex_replace(str, std::regex(R"(([^ ]+)I)"), "imag($1)");
                    result += "e" + std::to_string(leafMap.size()) + " := " + str + "\n";
                } else if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Predicate>)
                    result += "p" + std::to_string(leafMap.size()) + " := " + Convert::ToString(sym) + "\n";
                leafMap[sym] = leafMap.size();
            }
        }
    }

	// result += "\n";
	result += "Root States ";
    for (auto i : desc.finalStates) {
        result += std::to_string(i) + " ";
        // result += desc.stateNum.TranslateBwd(i) + " ";
    }
	// for_each(desc.finalStates.cbegin(), desc.finalStates.cend(),
	// 	[&result](const std::string& fsStr){ result += fsStr + " ";});

	result += "\n";
	result += "Transitions\n";

    for (const auto &t : desc.transitions) {
        for (const auto &t2 : t.second) {
            const auto &q = t2.first;
            for (const auto &in : t2.second) {
                if (t.first.is_leaf()) {
                    if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Concrete>)
                        result += "[c" + std::to_string(leafMap.at(t.first.symbol())) + "," + Convert::ToString(t.first.tag()) + "]";
                    else if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Symbolic>)
                        result += "[e" + std::to_string(leafMap.at(t.first.symbol())) + "," + Convert::ToString(t.first.tag()) + "]";
                    else if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Predicate>)
                        result += "[p" + std::to_string(leafMap.at(t.first.symbol())) + "," + Convert::ToString(t.first.tag()) + "]";
                } else if (std::is_convertible<Symbol, std::string>::value)
                    result += "[" + Convert::ToString(t.first) + "]";
                else
                    result += Convert::ToString(t.first);
                if (!(in.empty())) {
                    result += "(";
                    result += std::to_string(in[0]); //desc.stateNum.TranslateBwd(in[0]);
                    for (size_t i = 1; i < in.size(); ++i) {
                        result += ", ";
                        result += std::to_string(in[i]); //desc.stateNum.TranslateBwd(in[i]);
                    }
                    result += ")";
                }
                result += " -> ";
                result += std::to_string(q); //desc.stateNum.TranslateBwd(finalSet);
                result += "\n";
            }
        }
    }

	return result;
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template std::string TimbukSerializer::Serialize(TreeAutomata desc);
template std::string TimbukSerializer::Serialize(SymbolicAutomata desc);
template std::string TimbukSerializer::Serialize(PredicateAutomata desc);
template std::string TimbukSerializer::Serialize(IndexAutomata desc);