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

namespace VATA
{
	namespace Util
	{
		struct TreeAutomata;
	}
}

struct CompareSymbolName {
    bool operator()(const std::vector<int> &lhs, const std::vector<int> &rhs) const {
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
	typedef std::vector<State> StateVector;
	typedef std::set<State> StateSet;

	typedef std::vector<int> Symbol;
    typedef std::map<Symbol, std::map<StateVector, StateSet>, CompareSymbolName> TransitionMap;

public:   // data members
		std::string name;
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

	std::string ToString() const
	{
		std::string result;
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
    bool is_same_partition(const std::vector<int> &state_to_partition_id, State a, State b);
    TreeAutomata binary_operation(const TreeAutomata &o, bool add);
    void swap_forward(const int k);
    void swap_backward(const int k);
    void fraction_simplication();

public:
    void determinize();
    void minimize();
    void integer_multiplication(int m);
    void omega_multiplication();
    void divide_by_the_square_root_of_two();
    void branch_restriction(int k, bool positive_has_value=true);
    void value_restriction(int k, bool branch);
    void semi_determinize();
    void semi_undeterminize();
    TreeAutomata operator+(const TreeAutomata &o) { return binary_operation(o, true); }
    TreeAutomata operator-(const TreeAutomata &o) { return binary_operation(o, false); }
    void print();

    void X(int t);
    void Y(int t);
    void Z(int t);
    void H(int t);
    void S(int t);
    void T(int t);
    void CZ(int c, int t);

    /* Produce an automaton instance. */
    static TreeAutomata uniform(int n);
    static TreeAutomata classical(int n);
};

#endif
