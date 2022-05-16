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
using VATA::Serialization::TimbukSerializer;

// Standard library headers
#include <algorithm>

using std::for_each;


std::string TimbukSerializer::Serialize(const TreeAutomata& desc)
{
	std::string result;

	result += "Ops ";
	for (auto itSymb = desc.symbols.cbegin();
		itSymb != desc.symbols.cend(); ++itSymb)
	{
		result += VATA::Util::Convert::ToString(itSymb->first) + ":" +
			VATA::Util::Convert::ToString(itSymb->second) + " ";
	}

	result += "\n";
	result += "Automaton " + (desc.name.empty()? "anonymous" : desc.name);

	result += "\n";
	result += "States ";
    for (unsigned i=0; i<desc.stateNameToId.size(); i++) {
        result += desc.stateNameToId.TranslateBwd(i) + " ";
    }
	// for_each(desc.states.cbegin(), desc.states.cend(),
	// 	[&result](const std::string& sStr){ result += sStr + " ";});

	result += "\n";
	result += "Final States ";
    for (unsigned i : desc.finalStates) {
        result += desc.stateNameToId.TranslateBwd(i) + " ";
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
                    result += desc.stateNameToId.TranslateBwd(t2.first[0]);
                    for (size_t i = 1; i < t2.first.size(); ++i) {
                        result += ", ";
                        result += desc.stateNameToId.TranslateBwd(t2.first[i]);
                    }
                    result += ")";
                }
                result += " -> ";
                result += desc.stateNameToId.TranslateBwd(finalSet);
                result += "\n";
            }
        }
    }

	return result;
}
