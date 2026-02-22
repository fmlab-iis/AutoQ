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
#include <autoq/util/types.hh>
#include <autoq/util/qasm_regex.hh>
#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/symbol/predicate.hh"
#include "autoq/symbol/index.hh"
#include "autoq/symbol/constrained.hh"
#include "autoq/complex/constrained_complex.hh"
#include <map>

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
    typedef Automata<Symbol::Constrained> ConstrainedAutomata;
}

template <typename T> constexpr auto support_fraction_simplification = requires (T x) {
    x.fraction_simplification();
};

template <typename TT>
struct AUTOQ::Automata
{
// data types
    typedef int64_t State; // TODO: will make the program slightly slower. We wish to make another dynamic type.
	typedef std::vector<State> StateVector;
	typedef std::set<State> StateSet;

    typedef TT Symbol;
	typedef unsigned long long Tag;
    inline static constexpr auto Tag_MAX = static_cast<Tag>(1) << (std::numeric_limits<Tag>::digits - 1);
    typedef std::pair<Symbol, Tag> stdpairSymbolTag;
    // in a transition of a form (Symbol, Tag)[q1, ..., qn] -> q
    // Symbol represents the qbit and tag represent the color
    // color is a bitset, where the i-th bit is 1 if the i-th color is used
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
        Tag tag_intersection(Tag other) const { return this->second & other; }
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
            os << "[" << obj.symbol() << "," << obj.tag() << "]"; // print only the symbol part without the tag
            return os;
        }
    };
    // access transition with pair (qubit, color), get a map that satisfies this
    // the map contains set of transitions parent -> set of state vectors
    typedef std::map<SymbolTag, std::map<State, std::set<StateVector>>> TopDownTransitions;
    typedef std::map<SymbolTag, std::map<StateVector, StateSet>> BottomUpTransitions;
    typedef std::vector<std::map<Tag, std::map<State, std::set<StateVector>>>> InternalTopDownTransitions; // Keys range from 1 to qubit().

// data members
    std::string name;
    StateVector finalStates;
    State stateNum;
    int qubitNum;
    int symbolicvarsNum;
	TopDownTransitions transitions;
    std::set<std::string> vars;
    std::string constraints;
    bool hasLoop;
    bool isTopdownDeterministic;
    inline static int gateCount, stateBefore, transitionBefore;
    inline static bool gateLog, opLog;
    inline static std::string include_status;
    inline static std::chrono::steady_clock::duration binop_time, branch_rest_time, value_rest_time;
    inline static std::chrono::steady_clock::duration total_gate_time, total_removeuseless_time, total_reduce_time, total_include_time;
    inline static std::chrono::time_point<std::chrono::steady_clock> start_execute, stop_execute;
    inline static std::chrono::time_point<std::chrono::steady_clock> startFromFileToAutomata, endFromFileToAutomata;
    /* Notice inline is very convenient for declaring and defining a static member variable together! */

// methods
    /****************************/
	Automata() : // initialization
        name(),
		finalStates(),
        stateNum(0),
        qubitNum(0),
        symbolicvarsNum(0),
		transitions(),
        vars(),
        constraints(),
        hasLoop(false),
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

	/******************************************************/
    /* inclusion.cc: checks language inclusion of two TAs */
    bool operator_scaled_inclusion_with_renaming(Automata o) const;
    bool operator<<=(Automata o) const;
    bool operator>>=(const Automata &o) const { return o <<= *this; }
    bool operator<=(const Automata &o) const;
    bool operator>=(const Automata &o) const { return o <= *this; }
	bool operator==(const Automata &o) const { return (*this <= o) && (o <= *this); }
    bool operator!=(const Automata &o) const { return !(*this == o); }
    bool operator<(const Automata &o) const { return (*this <= o) && !(o <= *this); }
    bool operator>(const Automata &o) const { return o < *this; }
    // The above comparison is done after amplitude comparison.
    bool empty() const;
    /******************************************************/

    /******************************************************************/
    /* parameterized.cc: auxiliary operations for parameterized gates */
    void unfold_top();
    void unfold_bottom();
    void fold();
    /******************************************************************/

    /********************************************/
    /* reduce.cc: applying reduction algorithms */
    void sim_reduce();
    void bottom_up_reduce(int starts_from_depth=INT_MAX);
    void union_all_colors_for_a_given_transition();
    bool light_reduce_up(); /// lightweight size reduction, done upwards; returns @p true iff the automaton changed
    bool light_reduce_up_iter(); /// lightweight upwareds size reduction, iterated until change happens, returns @p true iff the automaton changed
    bool light_reduce_down(); /// lightweight size reduction, done downwards; returns @p true iff the automaton changed
    bool light_reduce_down_iter(); /// lightweight downwards size reduction, iterated until change happens, returns @p true iff the automaton changed
    void reduce(); /// reduces the automaton using a preferred reduction
    void remove_useless(bool only_bottom_up=false);
    void state_renumbering();
    void k_unification();
    void fraction_simplification() requires support_fraction_simplification<TT>;
    /********************************************/

    /**************************************/
    /* gate.cc: quantum gates abstraction */
private:
    void General_Single_Qubit_Gate(int t, const std::function<Symbol(const Symbol&, const Symbol&)> &u1u2, const std::function<Symbol(const Symbol&, const Symbol&)> &u3u4);
    void General_Controlled_Gate(int c, int t, const std::function<Symbol(const Symbol&, const Symbol&)> &u1u2, const std::function<Symbol(const Symbol&, const Symbol&)> &u3u4, const std::function<Symbol(const Symbol&)> &multiply_by_c0 = ([](const Symbol &l) -> Symbol { return l; }));
    void General_Controlled_Gate(int c, int c2, int t, const std::function<Symbol(const Symbol&, const Symbol&)> &u1u2, const std::function<Symbol(const Symbol&, const Symbol&)> &u3u4, const std::function<Symbol(const Symbol&)> &multiply_by_c0 = ([](const Symbol &l) -> Symbol { return l; }));
    void Diagonal_Gate(int t, const std::function<void(Symbol*)> &multiply_by_c0, const std::function<void(Symbol*)> &multiply_by_c1);
public:
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
    void randG(int G, int A, int B=0, int C=0);
    void Tdg(int t);
    void Sdg(int t);
    void Swap(int t1, int t2);
    void CX();
    void CX_inv();
    void Phase(const boost::rational<boost::multiprecision::cpp_int> &r);
    void CK(int c, int t);
    Automata measure(int t, bool outcome) const;
    /**************************************/

    /*******************************************/
    /* instance.cc: produce automata instances */
    static Automata uniform(int n);
    static Automata basis(int n);
    static Automata prefix_basis(int n);
    static Automata random(int n);
    static Automata zero(int n);
    static Automata zero_amplitude(int n);
    static Automata basis_zero_one_zero(int n);
    static Automata zero_zero_one_zero(int n);
    static Automata zero_one_zero(int n);
    static ConstrainedAutomata efficiently_construct_singleton_lsta(
        const std::map<std::string, AUTOQ::Complex::ConstrainedComplex> &ket2amp);
    /*******************************************/

    /****************************************************/
    /* execute.cc: the main function for gate execution */
    void single_gate_execute(const std::string& line, const QasmRegexes& re, const std::vector<int>& qubit_permutation);
    bool execute(const std::string &filename, std::vector<int> qubit_permutation={}, const std::vector<AUTOQ::Automata<Symbol>> &loopInvariants={}, ParameterMap params={});
    bool execute(const char *filename, std::vector<int> qubit_permutation={}, const std::vector<AUTOQ::Automata<Symbol>> &loopInvariants={}, ParameterMap params={});
    static std::string check_the_invariants_types(const std::string& filename);
private:
    /** Handles a closing "}" in QASM: end of while, or if-block, or else-block. */
    void handle_closing_brace(bool& inWhileLoop, bool& inIfBlock, bool& inElseBlock,
        const std::string& previous_line, const std::string& while_measurement_guard,
        Automata<Symbol>& I, Automata<Symbol>& measure_to_break, Automata<Symbol>& measure_to_else,
        Automata<Symbol>& result_after_if, bool& verify);
    /** Handles "while (var) {": load invariant, check inclusion, set measure_to_continue/break, *this. */
    void handle_while_loop_start(const std::string& line, const std::string& previous_line,
        const std::vector<Automata<Symbol>>& loopInvariants, int& loopInvariantCounter,
        bool& inWhileLoop, std::string& while_measurement_guard,
        const std::map<std::string, int>& var_is_measure_what_qubit,
        Automata<Symbol>& I, Automata<Symbol>& measure_to_continue, Automata<Symbol>& measure_to_break, bool& verify);
    /** Handles "if (var) {": split by measurement, set measure_to_else and *this. */
    void handle_if_block_start(const std::string& line, const std::string& previous_line,
        const std::map<std::string, int>& var_is_measure_what_qubit,
        Automata<Symbol>& measure_to_else);
    /** Handles "else {": switch to the other branch. */
    void handle_else(const Automata<Symbol>& measure_to_else);
public:
    /****************************************************/

    /**************************************************/
    /* query.cc: all utility functions related to TAs */
    void initialize_stats();
    void print_aut(const std::string &prompt="") const;
    void print_stats(const std::string &str="", bool newline=false);
    void print_language(const std::string &prompt="") const;
    int count_leaves() const;
    int count_states() const;
    int count_transitions() const;
    /**************************************************/

    /**************************************************/
    /* general.cc: all general operations for two TAs */
    Automata operator*(Automata aut2) const; // use the multiplication operator to denote "tensor product"
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Weffc++"
    Automata operator||(const Automata &o) const; // use the logical OR operator to denote "union"
    Automata operator&&(const Automata &o) const; // use the logical AND operator to denote "intersection"
    #pragma GCC diagnostic pop
    void SwapDown(int q);
    void SwapUp(int q);
    /**************************************************/
};


namespace std {
#define AUTOQ_HASH_SYMBOL_TAG(AutType) \
    template <> struct hash<typename AUTOQ::AutType::SymbolTag> { \
        size_t operator()(const AUTOQ::AutType::SymbolTag& obj) const { \
            std::size_t seed = 0; \
            boost::hash_combine(seed, obj.first); \
            boost::hash_combine(seed, obj.second); \
            return seed; \
        } \
    }
    AUTOQ_HASH_SYMBOL_TAG(TreeAutomata);
    AUTOQ_HASH_SYMBOL_TAG(SymbolicAutomata);
    AUTOQ_HASH_SYMBOL_TAG(PredicateAutomata);
    AUTOQ_HASH_SYMBOL_TAG(IndexAutomata);
    AUTOQ_HASH_SYMBOL_TAG(ConstrainedAutomata);
#undef AUTOQ_HASH_SYMBOL_TAG
}

// bool operator<=(const AUTOQ::SymbolicAutomata &autA, const AUTOQ::PredicateAutomata &autB);

#endif
