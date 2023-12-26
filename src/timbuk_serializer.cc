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
#include <autoq/autoq.hh>
#include <autoq/symbol/concrete.hh>
#include <autoq/symbol/symbolic.hh>
#include <autoq/symbol/predicate.hh>
#include <autoq/serialization/timbuk_serializer.hh>

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
    if constexpr(!std::is_same_v<Symbol, AUTOQ::Symbol::Predicate>) {
        desc.fraction_simplification();
    }

	std::string result;
	result += "Ops ";
	for (auto itSymb = desc.transitions.cbegin();
		itSymb != desc.transitions.cend(); ++itSymb)
	{
        if (std::is_convertible<Symbol, std::string>::value)
            result += "[" + AUTOQ::Util::Convert::ToString(itSymb->first) + "]:" +
			    AUTOQ::Util::Convert::ToString(itSymb->second.begin()->second.begin()->size()) + " ";
        else
		    result += AUTOQ::Util::Convert::ToString(itSymb->first) + ":" +
			    AUTOQ::Util::Convert::ToString(itSymb->second.begin()->second.begin()->size()) + " ";
	}

	result += "\n";
	result += "Automaton " + (desc.name.empty()? "anonymous" : desc.name);

	result += "\n";
	result += "States ";
    for (auto i=0; i<desc.stateNum; i++) {
        result += std::to_string(i) + " ";
        // result += desc.stateNum.TranslateBwd(i) + " ";
    }
	// for_each(desc.states.cbegin(), desc.states.cend(),
	// 	[&result](const std::string& sStr){ result += sStr + " ";});

	result += "\n";
	result += "Final States ";
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
                if (std::is_convertible<Symbol, std::string>::value)
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