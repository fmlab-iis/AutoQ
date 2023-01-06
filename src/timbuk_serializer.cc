/*****************************************************************************
 *  VATA Tree Automata Library
 *
 *  Copyright (c) 2011  Ondra Lengal <ilengal@fit.vutbr.cz>
 *
 *  Description:
 *    Implementation file for a serializer of automata to Timbuk format.
 *
 *****************************************************************************/

// VATA headers
#include <vata/vata.hh>
#include <vata/serialization/timbuk_serializer.hh>

using VATA::Util::Convert;
using VATA::Util::Automata;
using VATA::Util::TreeAutomata;
using VATA::Serialization::TimbukSerializer;

// Standard library headers
#include <algorithm>

using std::for_each;

template <typename InitialSymbol>
std::string TimbukSerializer::Serialize(const Automata<InitialSymbol>& desc)
{
	std::string result;

	result += "Ops ";
	for (auto itSymb = desc.transitions.cbegin();
		itSymb != desc.transitions.cend(); ++itSymb)
	{
		result += VATA::Util::Convert::ToString(itSymb->first) + ":" +
			VATA::Util::Convert::ToString(itSymb->second.begin()->first.size()) + " ";
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
            for (const auto &finalSet : t2.second) {
                result += Convert::ToString(t.first);
                if (!(t2.first.empty())) {
                    result += "(";
                    result += std::to_string(t2.first[0]); //desc.stateNum.TranslateBwd(t2.first[0]);
                    for (size_t i = 1; i < t2.first.size(); ++i) {
                        result += ", ";
                        result += std::to_string(t2.first[i]); //desc.stateNum.TranslateBwd(t2.first[i]);
                    }
                    result += ")";
                }
                result += " -> ";
                result += std::to_string(finalSet); //desc.stateNum.TranslateBwd(finalSet);
                result += "\n";
            }
        }
    }

	return result;
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template std::string TimbukSerializer::Serialize(const TreeAutomata& desc);