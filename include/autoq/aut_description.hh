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
#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/symbol/predicate.hh"

namespace AUTOQ
{
    namespace Symbol
    {
        struct Concrete;
        struct Symbolic;
        struct Predicate;
    }
    template <typename TT> struct Automata;
    typedef Automata<Symbol::Concrete> TreeAutomata;
    typedef Automata<Symbol::Symbolic> SymbolicAutomata;
    typedef Automata<Symbol::Predicate> PredicateAutomata;
}

template <typename TT>
struct AUTOQ::Automata
{
// data types
    typedef int64_t State; // TODO: will make the program slightly slower. We wish to make another dynamic type.
	typedef std::vector<State> StateVector;
	typedef std::set<State> StateSet;

    typedef TT Symbol;
	typedef std::vector<int> Tag;
    typedef std::pair<Symbol, Tag> stdpairSymbolTag;
    struct SymbolTag : stdpairSymbolTag {
        using stdpairSymbolTag::stdpairSymbolTag; // inherit parent constructors
        // template<typename... Args> SymbolTag(Args... args) : stdpairSymbolTag({args...}, {}) {}
        // Reference: https://stackoverflow.com/a/32595916/11550178
        SymbolTag(const Symbol &sym) : stdpairSymbolTag(sym, {}) {}
        Symbol& symbol() & { return this->first; }
        const Symbol& symbol() const & { return this->first; }
        Tag& tag() & { return this->second; }
        const Tag& tag() const & { return this->second; }
        int& tag(int index) & { return this->second.at(index); }
        const int& tag(int index) const & { return this->second.at(index); }
        /*********************************************************/
        bool is_internal() const { return symbol().is_internal(); }
        bool is_leaf() const { return symbol().is_leaf(); }
        bool is_tagged() const { return !tag().empty(); }
        bool operator<(const SymbolTag &rhs) const {
            if (is_internal() && rhs.is_leaf()) return true;
            else if (is_leaf() && rhs.is_internal()) return false;
            else if (symbol() == rhs.symbol()) { // if symbol content is the same, compare tag
                // TODO: I still don't understand why "tag size" should also be compared first.
                if (tag().size() < rhs.tag().size())
                    return true;
                else if (tag().size() > rhs.tag().size())
                    return false;
                else
                    return tag() < rhs.tag();
            } // compare symbol content first
            else return symbol() < rhs.symbol();
        }
        friend std::ostream& operator<<(std::ostream& os, const SymbolTag& obj) {
            os << obj.symbol(); // print only the symbol part without the tag
            // os << obj.symbol() << AUTOQ::Util::Convert::ToString(obj.tag());
            return os;
        }
    };
    typedef std::map<SymbolTag, std::map<State, std::set<StateVector>>> TopDownTransitions;
    typedef std::map<SymbolTag, std::map<StateVector, StateSet>> BottomUpTransitions;

// data members
	unsigned qubitNum;
    std::string name;
    StateSet finalStates;
    State stateNum;
	TopDownTransitions transitions;
    std::set<std::string> vars;
    std::string constraints;

    inline static int gateCount;
    inline static bool gateLog, opLog;
    inline static bool disableRenumbering = false;
    inline static std::chrono::steady_clock::duration binop_time, branch_rest_time, value_rest_time;
    /* Notice inline is very convenient for declaring and defining a static member variable together! */

// methods
    /****************************/
	Automata() : // initialization
		qubitNum(),
        name(),
		finalStates(),
        stateNum(),
		transitions(),
        vars(),
        constraints()
	{ }
    /****************************/

	/******************************************************/
    /* inclusion.cc: checks language inclusion of two TAs */
    bool operator<=(const Automata &o) const;
    bool operator>=(const Automata &o) const { return o <= *this; }
	bool operator==(const Automata &o) const { return (*this <= o) && (o <= *this); }
    bool operator!=(const Automata &o) const { return !(*this == o); }
    bool operator<(const Automata &o) const { return (*this <= o) && !(o <= *this); }
    bool operator>(const Automata &o) const { return o < *this; }
    // The above comparison is done after fraction_simplification() is called.
    // The comparison below is done when global phases are allowed.
    bool operator<<=(Automata o) const;
    /******************************************************/

    /******************************************************/
    /* composition_based.cc: composition-based operations */
    void swap_forward(const int k);
    void swap_backward(const int k);
    void omega_multiplication(int rotation=1);
    void divide_by_the_square_root_of_two();
    void branch_restriction(int k, bool positive_has_value=true);
    void value_restriction(int k, bool branch);
    void semi_determinize();
    void semi_undeterminize();
    Automata operator+(const Automata &o) const;
    Automata operator-(const Automata &o) const;
    Automata operator*(int c) const;
    Automata operator||(const Automata &o) const; // use the logical OR operator to denote "union"
    /******************************************************/

    /********************************************/
    /* reduce.cc: applying reduction algorithms */
    bool light_reduce_up(); /// lightweight size reduction, done upwards; returns @p true iff the automaton changed
    bool light_reduce_up_iter(); /// lightweight upwareds size reduction, iterated until change happens, returns @p true iff the automaton changed
    bool light_reduce_down(); /// lightweight size reduction, done downwards; returns @p true iff the automaton changed
    bool light_reduce_down_iter(); /// lightweight downwards size reduction, iterated until change happens, returns @p true iff the automaton changed
    void reduce(); /// reduces the automaton using a prefered reduction
    void remove_useless(bool only_bottom_up=false);
    void state_renumbering();
    void k_unification();
    void fraction_simplification();
    /********************************************/

    /**********************************************/
    /* quantum_gate.cc: quantum gates abstraction */
    void X(int t);
    void Y(int t);
    void Z(int t, bool opt=true);
    void H(int t);
    void S(int t);
    void T(int t);
    void Rx(int t);
    void Ry(int t);
    void CX(int c, int t, bool opt=true);
    void CZ(int c, int t);
    void CCX(int c, int c2, int t);
    void randG(int G, int A, int B=0, int C=0);
    void Tdg(int t);
    void Sdg(int t);
    void swap(int t1, int t2);
    void CK(int c, int t);
    Automata measure(int t, bool outcome) const;
    /**********************************************/

    /***********************************************/
    /* aut_instance.cc: produce automata instances */
    static Automata uniform(int n);
    static Automata basis(int n);
    static Automata random(int n);
    static Automata zero(int n);
    static Automata zero_amplitude(int n);
    static Automata basis_zero_one_zero(int n);
    static Automata zero_zero_one_zero(int n);
    static Automata zero_one_zero(int n);
    /***********************************************/

    /****************************************************/
    /* execute.cc: the main function for gate execution */
    bool execute(const std::string& filename);
    static void check_the_invariants_types(const std::string& filename);
    /****************************************************/

    /**************************************************/
    /* query.cc: all utility functions related to TAs */
    int count_states() const;
    int count_transitions() const;
    void print(const std::string &prompt="") const;
    void print_language(const std::string &prompt="") const;
    /**************************************************/
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
}

#endif
