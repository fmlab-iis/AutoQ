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
#include <algorithm>
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

struct CompareSymbolName {
    bool operator()(const vector<int> &lhs, const vector<int> &rhs) const {
        if (lhs.size() < rhs.size())
            return true;
        else if (lhs.size() > rhs.size())
            return false;
        else
            return lhs < rhs;
    }
};

struct VATA::Util::TreeAutomata
{
public:   // data types
    typedef int State;
	typedef vector<State> StateVector;
	typedef set<State> StateSet;

	typedef vector<int> Symbol;
    typedef map<Symbol, map<StateVector, StateSet>, CompareSymbolName> TransitionMap;

public:   // data members
	string name;
    StateSet finalStates;
    int stateNum, qubitNum;
	TransitionMap transitions;

public:   // methods

	TreeAutomata() :
		name(),
		finalStates(),
        stateNum(),
        qubitNum(),
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
			(finalStates == rhs.finalStates) &&
            (stateNum == rhs.stateNum) &&
            (qubitNum == rhs.qubitNum) &&
			(transitions == rhs.transitions);
	}

	string ToString() const
	{
		string result;
		result += "name: " + name + "\n";
		result += "number of states: " + Convert::ToString(stateNum) + "\n";
		result += "final states: " + Convert::ToString(finalStates) + "\n";
		result += "transitions: \n";
		for (const auto &trans : transitions)
		{
			result += Convert::ToString(trans) + "\n";
		}

		return result;
	}

private:
    void remove_useless();
    bool is_same_partition(const vector<int> &state_to_partition_id, State a, State b);
    TreeAutomata binary_operation(const TreeAutomata &o, bool add);
    void swap_forward(const int k);
    void swap_backward(const int k);

public:
    void determinize();
    void minimize();
    void integer_multiplication(int m);
    void omega_multiplication();
    void branch_restriction(int k, bool positive_has_value=true);
    void semi_determinize();
    void semi_undeterminize();
    void value_restriction(int k, bool branch);
    TreeAutomata operator+(const TreeAutomata &o) { return binary_operation(o, true); }
    TreeAutomata operator-(const TreeAutomata &o) { return binary_operation(o, false); }

    void X(int t);
    void Z(int t);
    void S(int t);
    void T(int t);
    void CZ(int c, int t);

    /* Produce an automaton instance. */
    static TreeAutomata uniform(int n);
    static TreeAutomata classical(int n);
};

#endif
