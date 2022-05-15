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
		result += itSymb->first + ":" +
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
	for (auto itTran = desc.transitions.cbegin();
		itTran != desc.transitions.cend(); ++itTran)
        for (auto finalSet : itTran->second)
        {
            result += itTran->first.first;
            if (!(itTran->first.second.empty()))
            {
                result += "(";
                result += desc.stateNameToId.TranslateBwd(itTran->first.second[0]);
                for (size_t i = 1; i < itTran->first.second.size(); ++i)
                {
                    result += ", ";
                    result += desc.stateNameToId.TranslateBwd(itTran->first.second[i]);
                }

                result += ")";
            }

            result += " -> ";
            result += desc.stateNameToId.TranslateBwd(finalSet);

            result += "\n";
        }

	return result;
}
