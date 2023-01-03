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
#include <chrono>
#include <algorithm>
#include <vata/vata.hh>
#include <vata/util/triple.hh>
#include <vata/util/two_way_dict.hh>

#include <boost/multiprecision/cpp_int.hpp>

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
    typedef int64_t State; // TODO: will make the program slightly slower. We wish to make another dynamic type.
	typedef std::vector<State> StateVector;
	typedef std::set<State> StateSet;

	typedef boost::multiprecision::cpp_int SymbolEntry;
    typedef std::vector<SymbolEntry> Tag;
    typedef std::vector<SymbolEntry> stdvectorSymbolEntry;
    struct Symbol; // forward declaration for operator Symbol()
    struct InitialSymbol : stdvectorSymbolEntry {
        using stdvectorSymbolEntry::stdvectorSymbolEntry; // inherit parent constructors
        bool is_internal() const { return size() < 5; }
        bool is_leaf() const { return size() == 5; }
        friend std::ostream& operator<<(std::ostream& os, const InitialSymbol& obj) {
            os << VATA::Util::Convert::ToString(static_cast<stdvectorSymbolEntry>(obj));
            return os;
        }
        operator Symbol() const { return Symbol(*this, {}); }
    };
    typedef std::pair<InitialSymbol, Tag> stdpairInitialSymbolTag;
    struct Symbol : stdpairInitialSymbolTag {
        using stdpairInitialSymbolTag::stdpairInitialSymbolTag; // inherit parent constructors
        Symbol(SymbolEntry a) : stdpairInitialSymbolTag({a}, {}) {}
        Symbol(SymbolEntry a, SymbolEntry b, SymbolEntry c, SymbolEntry d, SymbolEntry e) : stdpairInitialSymbolTag({a,b,c,d,e}, {}) {}
        // Reference: https://stackoverflow.com/a/32595916/11550178
        InitialSymbol& initial_symbol() & { return first; }
        const InitialSymbol& initial_symbol() const & { return first; }
        SymbolEntry& initial_symbol(int index) & { return first.at(index); }
        const SymbolEntry& initial_symbol(int index) const & { return first.at(index); }
        Tag& tag() & { return second; }
        const Tag& tag() const & { return second; }
        SymbolEntry& tag(int index) & { return second.at(index); }
        const SymbolEntry& tag(int index) const & { return second.at(index); }
        /*********************************************************/
        size_t size() const { return initial_symbol().size() + tag().size(); }
        bool is_internal() const { return initial_symbol().is_internal(); }
        bool is_leaf() const { return initial_symbol().is_leaf(); }
        bool is_tagged() const { return !tag().empty(); }
        bool operator<(const Symbol &rhs) const {
            if (initial_symbol().size()+tag().size() < rhs.initial_symbol().size()+rhs.tag().size())
                return true;
            else if (initial_symbol().size()+tag().size() > rhs.initial_symbol().size()+rhs.tag().size())
                return false;
            else {
                auto v1 = initial_symbol();
                v1.insert(v1.end(), tag().begin(), tag().end());
                auto v2 = rhs.initial_symbol();
                v2.insert(v2.end(), rhs.tag().begin(), rhs.tag().end());
                return v1 < v2;
            }
            // if (is_internal() && rhs.is_leaf())
            //     return true;
            // if (is_leaf() && rhs.is_internal())
            //     return false;
            // else if (initial_symbol() == rhs.initial_symbol()) { // if symbol content is the same, compare tag
            //     if (tag().size() < rhs.tag().size())
            //         return true;
            //     else if (tag().size() > rhs.tag().size())
            //         return false;
            //     else
            //         return tag() < rhs.tag();
            // }
            // else // compare symbol content first
            //     return initial_symbol() < rhs.initial_symbol();
        }
        friend std::ostream& operator<<(std::ostream& os, const Symbol& obj) {
            os << obj.initial_symbol(); // print only the initial symbol
            return os;
        }
    };
    typedef std::map<Symbol, std::map<StateVector, StateSet>> TransitionMap;

public:   // data members
	std::string name;
    StateVector finalStates;
    State stateNum;
    int qubitNum;
	TransitionMap transitions;
    bool isTopdownDeterministic;
    inline static int gateCount;
    inline static bool gateLog, opLog;
    inline static std::chrono::steady_clock::duration binop_time, branch_rest_time, value_rest_time;
    /* Notice inline is very convenient for declaring and defining a static member variable together! */

public:   // methods

	TreeAutomata() :
		name(),
		finalStates(),
        stateNum(),
        qubitNum(),
		transitions(),
        isTopdownDeterministic(false)
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
    void remove_useless(bool only_bottom_up=false);
    TreeAutomata binary_operation(const TreeAutomata &o, bool add);
    void swap_forward(const int k);
    void swap_backward(const int k);

public:
    void fraction_simplication();
    void omega_multiplication(int rotation=1);
    void divide_by_the_square_root_of_two();
    void branch_restriction(int k, bool positive_has_value=true);
    void value_restriction(int k, bool branch);
    void semi_determinize();
    void semi_undeterminize();
    TreeAutomata operator+(const TreeAutomata &o) { return binary_operation(o, true); }
    TreeAutomata operator-(const TreeAutomata &o) { return binary_operation(o, false); }
    TreeAutomata Union(const TreeAutomata &o); // U is in uppercase since "union" is a reserved keyword.
    void print();
    int transition_size();

    /// simulation-based reduction
    void sim_reduce();
    /// lightweight size reduction, done upwards; returns @p true iff the automaton changed
    bool light_reduce_up();
    /// lightweight upwareds size reduction, iterated until change happens, returns @p true iff the automaton changed
    bool light_reduce_up_iter();
    /// lightweight size reduction, done downwards; returns @p true iff the automaton changed
    bool light_reduce_down();
    /// lightweight downwards size reduction, iterated until change happens, returns @p true iff the automaton changed
    bool light_reduce_down_iter();
    /// reduces the automaton using a prefered reduction
    void reduce();

    int count_transitions();
    void X(int t);
    void Y(int t);
    void Z(int t);
    void H(int t);
    void S(int t);
    void T(int t);
    void Rx(int t);
    void Ry(int t);
    void CNOT(int c, int t, bool opt=true);
    void CZ(int c, int t);
    void Toffoli(int c, int c2, int t);
    // void Fredkin(int c, int t, int t2);
    void randG(int G, int A, int B=0, int C=0);
    void Tdg(int t);
    void Sdg(int t);
    void swap(int t1, int t2);

    /* Produce an automaton instance. */
    static TreeAutomata uniform(int n);
    static TreeAutomata basis(int n);
    static TreeAutomata random(int n);
    static TreeAutomata zero(int n);
    static TreeAutomata basis_zero_one_zero(int n);
    static TreeAutomata zero_zero_one_zero(int n);
    static TreeAutomata zero_one_zero(int n);

    /* Equivalence Checking */
    static bool check_equal(const std::string& lhsPath, const std::string& rhsPath);
    static bool check_equal_aut(TreeAutomata lhs, TreeAutomata rhs);
    static bool check_inclusion(const std::string& lhsPath, const std::string& rhsPath);
};

namespace std {
//     template<> class numeric_limits<__int128_t> {
//         public:
//             static __int128_t max() {
//                 return (static_cast<__int128_t>(numeric_limits<__int64_t>::max()) << 64) + numeric_limits<__uint64_t>::max();
//             }
//             static __int128_t min() {
//                 return static_cast<__uint128_t>(1) << 127;
//             }
//             inline static int digits = 127;
//     };
//     template<> struct hash<__int128_t> {
//         size_t operator()(__int128_t var) const {
//             return std::hash<__uint64_t>{}(static_cast<__uint64_t>(var) ^ static_cast<__uint64_t>(var >> 64));
//         }
//     };
    template <> struct hash<typename VATA::Util::TreeAutomata::Symbol> {
        size_t operator()(const VATA::Util::TreeAutomata::Symbol& obj) const {
            std::size_t seed = 0;
            boost::hash_combine(seed, obj.first);
            boost::hash_combine(seed, obj.second);
            return seed;
        }
    };
}

#endif
