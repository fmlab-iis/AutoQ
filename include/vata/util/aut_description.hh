/*****************************************************************************
 *  VATA Tree Automata Library
 *
 *  Copyright (c) 2011  Ondra Lengal <ilengal@fit.vutbr.cz>
 *
 *  Description:
 *    Header file for class with automaton description.
 *
 *****************************************************************************/

#ifndef _VATA_AUT_DESCRIPTION_HH_
#define _VATA_AUT_DESCRIPTION_HH_

// VATA headers
#include <vata/vata.hh>
#include <vata/util/triple.hh>
#include <vata/util/two_way_dict.hh>

using namespace std;

namespace VATA
{
	namespace Util
	{
		struct TreeAutomata;
	}
}

struct VATA::Util::TreeAutomata
{
public:   // data types
    typedef std::string SymbolName;
	typedef std::pair<SymbolName, unsigned> Symbol; // 2nd element: arity

    typedef unsigned State;
	typedef std::vector<State> StateVector;
    typedef TwoWayDict<std::string, State> StateNameToIdMap;

    typedef std::set<Symbol> SymbolSet;
	typedef std::set<State> StateSet;
	typedef std::map<std::pair<SymbolName, StateVector>, State> TransitionMap;

public:   // data members

	std::string name;
    SymbolSet symbols;
	StateSet finalStates;
    StateNameToIdMap stateNameToId;
	TransitionMap transitions;

public:   // methods

	TreeAutomata() :
		name(),
		symbols(),
		finalStates(),
        stateNameToId(),
		transitions()
	{ }

	/**
	 * @brief  Relaxed equivalence check
	 *
	 * Checks whether the final states and transitions of two automata descriptions match.
	 */
	bool operator==(const TreeAutomata& rhs) const
	{
		return (finalStates == rhs.finalStates) && (transitions == rhs.transitions);
	}

	/**
	 * @brief  Strict equivalence check
	 *
	 * Checks whether all components of two automata descriptions match.
	 */
	bool StrictlyEqual(const TreeAutomata& rhs) const
	{
		return
			(name == rhs.name) &&
			(symbols == rhs.symbols) &&
			(finalStates == rhs.finalStates) &&
            // (stateNameToId == rhs.stateNameToId) &&
			(transitions == rhs.transitions);
	}

	std::string ToString() const
	{
		std::string result;
		result += "name: " + name + "\n";
		result += "symbols: " + Convert::ToString(symbols) + "\n";
		// result += "states: " + Convert::ToString(states) + "\n";
		result += "final states: " + Convert::ToString(finalStates) + "\n";
		result += "transitions: \n";
		for (auto trans : transitions)
		{
			result += Convert::ToString(trans) + "\n";
		}

		return result;
	}

    void minimize() {
        // int num_of_partition = 2;
        // std::map<string, int> partition;
        // for (auto s : states) partition[s] = 0;
        // for (auto s : finalStates) partition[s] = 1;

        // std::vector<TreeAutomata::Transition> vec_transitions(transitions.begin(), transitions.end());
        // bool changed = true;
        // while (changed) {
        //     changed = false;
        //     symbols.
        //     // for (int i=0; i<static_cast<int>(vec_transitions.size()); i++)
        //     //     for (int j=i+1; j<static_cast<int>(vec_transitions.size()); j++) {
        //     //         if (vec_transitions[i].first.size() == vec_transitions[j].first.size()) {
        //     //             for (int k=0; k<static_cast<int>(vec_transitions[i].first.size()); k++) {
        //     //                 bool others_are_the_same = true;
        //     //                 for (int z=0; z<static_cast<int>(vec_transitions[i].first.size()); z++) {
        //     //                     if (z!=k && vec_transitions[i].first[z]!=vec_transitions[j].first[z])
        //     //                         others_are_the_same = false;
        //     //                 }
        //     //                 if (others_are_the_same &&
        //     //                     vec_transitions[i].first[k] != vec_transitions[j].first[k] &&
        //     //                     partition[vec_transitions[i].first[k]] == partition[vec_transitions[j].first[k]] &&
        //     //                     partition[vec_transitions[i].third] != partition[vec_transitions[j].third]) {
        //     //                     partition[vec_transitions[i].first[k]] = num_of_partition; // j also OK
        //     //                     num_of_partition++;
        //     //                     changed = true;
        //     //                 }
        //     //             }
        //     //         }
        //     //     }
        // }
        // // for (auto s : states) std::cout << partition[s] << "\n";

        // std::map<int, string> mymap;
        // for (auto s : states) {
        //     if (mymap.find(partition[s]) == mymap.end())
        //         mymap[partition[s]] = s;
        // }

        // std::set<std::string>::iterator it = states.begin();
        // while (it != states.end()) {
        //     std::set<std::string>::iterator current = it++;
        //     if (mymap[partition[*current]] != *current)
        //         states.erase(*current);
        // }

        // std::set<std::string>::iterator it2 = finalStates.begin();
        // while (it2 != finalStates.end()) {
        //     std::set<std::string>::iterator current = it2++;
        //     if (mymap[partition[*current]] != *current)
        //         finalStates.erase(*current);
        // }

        // TreeAutomata::TransitionSet newSet;
        // for (auto t : vec_transitions) {
        //     TreeAutomata::StateVector st;
        //     for (auto s : t.first) {
        //         st.push_back(mymap[partition[s]]);
        //     }
        //     newSet.insert(TreeAutomata::Transition(st, t.second, mymap[partition[t.third]]));
        // }

        // transitions = newSet;
    }
};

#endif
