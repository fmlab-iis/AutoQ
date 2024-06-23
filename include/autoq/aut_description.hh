/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Copyright (c) 2011  Ondra Lengal <ilengal@fit.vutbr.cz>
 *
 *  Description:
 *    Header file for class with automaton description.
 *
 *****************************************************************************/

#ifndef _AUTOQ_AUT_DESCRIPTION_HH_
#define _AUTOQ_AUT_DESCRIPTION_HH_

// AUTOQ headers
#include <chrono>
#include <cstdlib>
#include <algorithm>
#include <autoq/autoq.hh>
#include <autoq/symbol/index.hh>
#include <autoq/symbol/concrete.hh>
#include <autoq/symbol/symbolic.hh>
#include <autoq/symbol/predicate.hh>
#include <autoq/util/triple.hh>
#include <autoq/util/two_way_dict.hh>
#include <boost/multiprecision/cpp_int.hpp>

namespace AUTOQ
{
    namespace Symbol
    {
        struct Concrete;
        struct Symbolic;
        struct Predicate;
        struct Index;
    }
    template <typename TT> struct Automata;
    typedef Automata<Symbol::Concrete> TreeAutomata;
    typedef Automata<Symbol::Symbolic> SymbolicAutomata;
    typedef Automata<Symbol::Predicate> PredicateAutomata;
    typedef Automata<Symbol::Index> IndexAutomata;
}

template <typename TT>
struct AUTOQ::Automata
{
public:   // data types
    typedef int64_t State; // TODO: will make the program slightly slower. We wish to make another dynamic type.
	typedef std::vector<State> StateVector;
	typedef std::set<State> StateSet;

    typedef TT Symbol;
	typedef unsigned Tag;
    inline static constexpr auto Tag_MAX = 1 << (std::numeric_limits<Tag>::digits - 1);
    typedef std::pair<Symbol, Tag> stdpairSymbolTag;
    struct SymbolTag : stdpairSymbolTag {
        using stdpairSymbolTag::stdpairSymbolTag; // inherit parent constructors
        // template<typename... Args> SymbolTag(Args... args) : stdpairSymbolTag({args...}, {}) {}
        // Reference: https://stackoverflow.com/a/32595916/11550178
        SymbolTag(const Symbol &sym) : stdpairSymbolTag(sym, 0) {}
        Symbol& symbol() & { return this->first; }
        const Symbol& symbol() const & { return this->first; }
        Tag& tag() & { return this->second; }
        const Tag& tag() const & { return this->second; }
        // bool& tag(int index) & { return this->second[index]; }
        bool tag(int index) const { return (this->second & (1<<index)) >> index; }
        /*********************************************************/
        bool is_internal() const { return symbol().is_internal(); }
        bool is_leaf() const { return symbol().is_leaf(); }
        // bool is_tagged() const { return !tag().empty(); }
        bool operator<(const SymbolTag &rhs) const {
            if (is_internal() && rhs.is_leaf()) return true;
            else if (is_leaf() && rhs.is_internal()) return false;
            else if (symbol() == rhs.symbol()) { // if symbol content is the same, compare tag
                // TODO: I still don't understand why "tag size" should also be compared first.
                // if (tag().size() < rhs.tag().size())
                //     return true;
                // else if (tag().size() > rhs.tag().size())
                //     return false;
                // else
                    return tag() < rhs.tag();
            } // compare symbol content first
            else return symbol() < rhs.symbol();
        }
        friend std::ostream& operator<<(std::ostream& os, const SymbolTag& obj) {
            os << obj.symbol() << "[" << obj.tag() << "]"; // print only the symbol part without the tag
            return os;
        }
    };
    typedef std::map<SymbolTag, std::map<State, std::set<StateVector>>> TransitionMap;
    typedef std::vector<std::map<Tag, std::map<State, std::set<StateVector>>>> InternalTransitionMap; // Keys range from 1 to qubit().

public:   // data members
	std::string name;
    StateVector finalStates;
    State stateNum;
    unsigned qubitNum;
	TransitionMap transitions;
    bool isTopdownDeterministic;
    inline static int gateCount, stateBefore, transitionBefore;
    inline static bool gateLog, opLog;
    inline static std::string include_status;
    inline static std::chrono::steady_clock::duration binop_time, branch_rest_time, value_rest_time;
    inline static std::chrono::steady_clock::duration total_gate_time, total_removeuseless_time, total_reduce_time, total_include_time;
    inline static std::chrono::time_point<std::chrono::steady_clock> start_execute, stop_execute;
    /* Notice inline is very convenient for declaring and defining a static member variable together! */

public:   // methods

	Automata() :
		name(),
		finalStates(),
        stateNum(0),
        qubitNum(0),
		transitions(),
        isTopdownDeterministic(false)
	{
        auto envptr = std::getenv("LOG");
        if (envptr != nullptr) {
            auto envstr = std::string(envptr);
            if (envstr.find("gate") != std::string::npos) {
                gateLog = true;
            }
            if (envstr.find("op") != std::string::npos) {
                opLog = true;
            }
        }
    }

	/**
	 * @brief  Relaxed equivalence check
	 *
	 * Checks whether the final states and transitions of two automata descriptions match.
	 */
	bool operator==(const Automata& rhs) const
	{
		return (finalStates == rhs.finalStates) && (transitions == rhs.transitions);
	}

	/**
	 * @brief  Strict equivalence check
	 *
	 * Checks whether all components of two automata descriptions match.
	 */
	bool StrictlyEqual(const Automata& rhs) const
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
		result += "number of states: " + Util::Convert::ToString(stateNum) + "\n";
		result += "final states: " + Util::Convert::ToString(finalStates) + "\n";
		result += "transitions: \n";
		for (const auto &trans : transitions)
		{
			result += Util::Convert::ToString(trans) + "\n";
		}

		return result;
	}

private:
    void state_renumbering();
    // void remove_impossible_colors();
    // void remove_useless(bool only_bottom_up=false);
    // Automata binary_operation(const Automata &o, bool add);
    // void swap_forward(const int k);
    // void swap_backward(const int k);
    void General_Single_Qubit_Gate(int t, const std::function<Symbol(const Symbol&, const Symbol&)> &u1u2, const std::function<Symbol(const Symbol&, const Symbol&)> &u3u4);
    void General_Controlled_Gate(int c, int t, const std::function<Symbol(const Symbol&, const Symbol&)> &u1u2, const std::function<Symbol(const Symbol&, const Symbol&)> &u3u4);
    void General_Controlled_Gate(int c, int c2, int t, const std::function<Symbol(const Symbol&, const Symbol&)> &u1u2, const std::function<Symbol(const Symbol&, const Symbol&)> &u3u4);
    void diagonal_gate(int t, const std::function<void(Symbol*)> &multiply_by_c0, const std::function<void(Symbol*)> &multiply_by_c1);
    void initialize_stats();

public:
    void fraction_simplification();
    void omega_multiplication(int rotation=1);
    void divide_by_the_square_root_of_two();
    // void branch_restriction(int k, bool positive_has_value=true);
    // void value_restriction(int k, bool branch);
    // void semi_determinize();
    // void semi_undeterminize();
    // Automata operator+(const Automata &o);
    // Automata operator-(const Automata &o);
    Automata Union(const Automata &o); // U is in uppercase since "union" is a reserved keyword.
    void print_aut(const char *str="") const;
    void print_stats(const std::string &str="", bool newline=false);
    int transition_size() const;
    int leaf_size() const;

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
    void union_all_colors_for_a_given_transition();

    int count_transitions();
    void X(int t);
    void Y(int t);
    void Z(int t, bool opt=true);
    void H(int t);
    void S(int t);
    void T(int t);
    void Rx(const boost::rational<boost::multiprecision::cpp_int> &theta, int t);
    void Ry(int t);
    void Rz(const boost::rational<boost::multiprecision::cpp_int> &theta, int t);
    void CX(int c, int t, bool opt=true);
    void CZ(int c, int t);
    void CCX(int c, int c2, int t);
    // void Fredkin(int c, int t, int t2);
    void randG(int G, int A, int B=0, int C=0);
    void Tdg(int t);
    void Sdg(int t);
    void swap(int t1, int t2);

    /* Produce an automaton instance. */
    static Automata uniform(int n);
    static Automata basis(int n);
    static Automata prefix_basis(int n);
    static Automata random(int n);
    static Automata zero(int n);
    static Automata basis_zero_one_zero(int n);
    static Automata zero_zero_one_zero(int n);
    static Automata zero_one_zero(int n);

    /* Equivalence Checking */
    static bool check_equal(const Automata& autA, const Automata& autB);
    // static bool check_equal_aut(Automata lhs, Automata rhs);
    // static bool check_inclusion(const std::string& lhsPath, const std::string& rhsPath);
    // static bool check_inclusion(const Automata& lhsPath, const std::string& rhsPath);
    // static bool check_inclusion(const std::string& lhsPath, const Automata& rhsPath);
    static bool check_inclusion(const Automata &autA, const Automata &autB);

    void execute(const std::string& filename);
    void execute(const char *filename);
    // void reverse_execute(const char *filename);
    void print_language(const char *str="") const;
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
    template <> struct hash<typename AUTOQ::TreeAutomata::SymbolTag> {
        size_t operator()(const AUTOQ::TreeAutomata::SymbolTag& obj) const {
            std::size_t seed = 0;
            boost::hash_combine(seed, obj.first);
            boost::hash_combine(seed, obj.second);
            return seed;
        }
    };
    template <> struct hash<typename AUTOQ::SymbolicAutomata::SymbolTag> {
        size_t operator()(const AUTOQ::SymbolicAutomata::SymbolTag& obj) const {
            std::size_t seed = 0;
            boost::hash_combine(seed, obj.first);
            boost::hash_combine(seed, obj.second);
            return seed;
        }
    };
    template <> struct hash<typename AUTOQ::IndexAutomata::SymbolTag> {
        size_t operator()(const AUTOQ::IndexAutomata::SymbolTag& obj) const {
            std::size_t seed = 0;
            boost::hash_combine(seed, obj.first);
            boost::hash_combine(seed, obj.second);
            return seed;
        }
    };
}

#endif
