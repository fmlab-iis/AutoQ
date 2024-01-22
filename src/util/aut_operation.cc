#include <autoq/aut_description.hh>
#include <autoq/complex/complex.hh>
#include <autoq/symbol/concrete.hh>
#include <autoq/symbol/symbolic.hh>
#include <autoq/symbol/predicate.hh>
#include <autoq/util/util.hh>
#include <autoq/inclusion.hh>
#include <autoq/parsing/timbuk_parser.hh>
#include <autoq/serialization/timbuk_serializer.hh>

#include "simulation/explicit_lts.hh"

#include <fstream>
#include <numeric>
#include <chrono>
#include <queue>
#include <regex>
#include <bit>
#include <filesystem>
#include <boost/dynamic_bitset.hpp>

using namespace AUTOQ;
using namespace AUTOQ::Util;
using AUTOQ::Symbol::Concrete;
using AUTOQ::Serialization::TimbukSerializer;

// using State                   = TreeAutomata::State;
// using StateSet                = TreeAutomata::StateSet;
// using StateVector             = TreeAutomata::StateVector;
// using SymbolTag                  = TreeAutomata::SymbolTag;
// using TransitionMap           = TreeAutomata::TransitionMap;

// using DiscontBinaryRelOnStates= DiscontBinaryRelation<State>;
// using StateToIndexMap         = std::unordered_map<State, size_t>;
// using StateToIndexTranslWeak  = Util::TranslatorWeak<StateToIndexMap>;
// using StateToStateMap         = std::unordered_map<State, State>;
// using StateToStateTranslWeak  = Util::TranslatorWeak<StateToStateMap>;

namespace {

  /**
   * @brief  Combine two hash values
   *
   * Values taken from
   * http://www.boost.org/doc/libs/1_64_0/boost/functional/hash/hash.hpp
   *
   * TODO: fix to be more suitable for 64b
   */
  template <class T>
  inline size_t hash_combine(size_t lhs, const T& rhs)
  {
    size_t rhs_hash = std::hash<T>{}(rhs);
    lhs ^= rhs_hash + 0x9e3779b9 + (lhs<<6) + (lhs>>2);
    return lhs;
  }

  /**
   * @brief  Hashes a range
   *
   * Inspired by
   * http://www.boost.org/doc/libs/1_64_0/boost/functional/hash/hash.hpp
   */
  template <typename It>
  size_t hash_range(It first, It last)
  {
    size_t accum = 0;
    for (; first != last; ++first) {
      accum = hash_combine(accum, *first);
    }

    return accum;
  }
} // anonymous namespace

namespace std
{
  /**
   * @brief  A hasher for vectors
   */
  template <class A>
  struct hash<std::vector<A>>
  {
    inline size_t operator()(const std::vector<A>& cont) const
    {
      return hash_range(cont.begin(), cont.end());
    }
  };
} // namespace std

template <typename InitialSymbol>
void AUTOQ::Automata<InitialSymbol>::state_renumbering() {
    if (disableRenumbering) return;
    TransitionMap transitions_new;
    std::map<State, State> stateOldToNew;
    for (const auto &t : transitions) {
        for (const auto &out_ins : t.second) {
            const auto &out = out_ins.first;
            State newOut = stateOldToNew.size();
            auto itBoolPair = stateOldToNew.insert({out, newOut});
            if (!itBoolPair.second) { // if insertion didn't happened
                const auto& it = itBoolPair.first;
                newOut = it->second;
            }
            for (auto in : out_ins.second) {
                for (auto &e : in) {
                    State newS = stateOldToNew.size();
                    auto itBoolPair = stateOldToNew.insert({e, newS});
                    if (!itBoolPair.second) { // if insertion didn't happened
                        const auto& it = itBoolPair.first;
                        newS = it->second;
                    }
                    e = newS;
                }
                transitions_new[t.first][newOut].insert(in);
            }
        }
    }
    transitions = transitions_new;
    StateSet finalStates_new;
    for (const auto &s : finalStates) {
        auto it = stateOldToNew.find(s);
        if (it != stateOldToNew.end()) {
            finalStates_new.insert(it->second);
        }
        // We do not add the untouched final states here, since
        // it could severely degrade the performance (either with or without sim_reduce()).
    }
    finalStates = finalStates_new;
    stateNum = stateOldToNew.size();
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::remove_useless(bool only_bottom_up) {
    auto start = std::chrono::steady_clock::now();
    // remove_impossible_colors();

    /*********************************
     * Part 0: Top-Down Data Structure
     *********************************/
    std::map<State, std::map<StateVector, std::set<SymbolTag>>> qifc;
    for (const auto &tr : transitions) {
        const auto &symbol_tag = tr.first;
        for (const auto &out_ins : tr.second) {
            const auto &out = out_ins.first;
            for (const auto &in : out_ins.second) {
                qifc[out][in].insert(symbol_tag);
            }
        }
    }

    /******************
     * Part 1: Top-Down
     ******************/
    std::vector<bool> traversed(stateNum, false);
    if (!only_bottom_up) {
        std::map<State, std::map<StateVector, std::set<SymbolTag>>> qifc2;
        std::queue<State> bfs(std::queue<State>::container_type(finalStates.begin(), finalStates.end()));
        while (!bfs.empty()) {
            auto top = bfs.front();
            bfs.pop();
            traversed[top] = true; // set flags for final states
            for (const auto &in_ : qifc[top]) {
                const auto &in = in_.first;
                for (const auto &s : in) {
                    if (!traversed[s]) {
                        traversed[s] = true;
                        bfs.push(s);
                    }
                }
            }
            qifc2[top] = qifc[top];
        }
        qifc = qifc2;
    }

    /*******************
     * Part 2: Bottom-Up
     *******************/
    traversed = std::vector<bool>(stateNum, false);
    TransitionMap transitions_new;
    bool changed;
    do {
        changed = false;
        for (const auto &q_ : qifc) {
            const auto &q = q_.first;
            for (const auto &in_ : q_.second) {
                const auto &in = in_.first;
                bool children_traversed = in.empty();
                if (!children_traversed) { // has children!
                    children_traversed = true;
                    for (const auto &s : in) {
                        if (!traversed[s]) {
                            children_traversed = false;
                            break;
                        }
                    }
                }
                if (children_traversed) {
                    if (!traversed[q]) {
                        traversed[q] = true;
                        changed = true;
                    }
                }
            }
        }
    } while(changed);
    for (const auto &q_ : qifc) {
        const auto &q = q_.first;
        if (!traversed[q]) continue; // ensure q is traversed
        for (const auto &in_ : q_.second) {
            const auto &in = in_.first;
            bool children_traversed = true;
            for (const auto &s : in) {
                if (!traversed[s]) {
                    children_traversed = false;
                    break;
                }
            }
            if (children_traversed) {
                for (const auto &symbol_tag : in_.second) {
                    transitions_new[symbol_tag][q].insert(in);
                }
            }
        }
    }
    transitions = transitions_new;
    StateSet finalStates_new;
    for (const auto &s : finalStates) {
        if (traversed[s])
            finalStates_new.insert(s);
    }
    finalStates = finalStates_new;

    /*********************
     * Part 3: Renumbering
     *********************/
    state_renumbering();
    auto duration = std::chrono::steady_clock::now() - start;
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::omega_multiplication(int rotation) {
    TransitionMap transitions_new;
    for (const auto &t_old : transitions) {
        const SymbolTag &symbol_tag = t_old.first;
        if (symbol_tag.is_leaf()) {
            SymbolTag s = symbol_tag;
            /************************** rotation **************************/
            s.symbol().omega_multiplication(rotation);
            transitions_new[s] = t_old.second;
        } else {
            assert(symbol_tag.tag().size() <= 1);
            transitions_new.insert(t_old);
        }
    }
    transitions = transitions_new;
    // DO NOT reduce here.
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::divide_by_the_square_root_of_two() {
    std::vector<SymbolTag> to_be_removed;
    TransitionMap to_be_inserted;
    for (const auto &t : transitions) {
        const SymbolTag &symbol_tag = t.first;
        if (symbol_tag.is_leaf()) {
            to_be_removed.push_back(symbol_tag);
            SymbolTag s = symbol_tag;
            s.symbol().divide_by_the_square_root_of_two();
            to_be_inserted[s] = t.second;
        }
    }
    for (const auto &t : to_be_removed)
        transitions.erase(t);
    for (const auto &t : to_be_inserted)
        transitions.insert(t);
    // fraction_simplification();
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::branch_restriction(int k, bool positive_has_value) {
    auto start = std::chrono::steady_clock::now();
    State num_of_states = stateNum;
    if (stateNum > std::numeric_limits<State>::max() / 2)
        throw std::overflow_error("[ERROR] The number of states is too large.");
    stateNum *= 2;

    TransitionMap transitions_copy = transitions;
    for (const auto &t : transitions_copy) {
        const SymbolTag &symbol_tag = t.first;
        if (symbol_tag.is_internal()) { // x_i + determinized number
            auto &out_ins_dest = transitions.at(symbol_tag);
            for (const auto &out_ins : t.second) {
                std::set<StateVector> ins;
                for (auto in : out_ins.second) {
                    for (auto &n : in)
                        n += num_of_states; // add $num_of_states to each element
                    ins.insert(in);
                }
                out_ins_dest[out_ins.first + num_of_states] = ins; // duplicate this internal transition
            }
        } else { // (a,b,c,d,k)
            assert(symbol_tag.is_leaf());
            for (const auto &out_ins : t.second) {
                assert(out_ins.second.size() == 1);
                assert(out_ins.second.begin()->empty());
                SymbolTag s = symbol_tag;
                s.symbol().back_to_zero(); // Note we do not change k.
                transitions[s][out_ins.first + num_of_states].insert({{}}); // duplicate this leaf transition
            }
        }
    }

    for (auto &t : transitions) {
        const SymbolTag &symbol_tag = t.first;
        if (symbol_tag.is_internal() && symbol_tag.symbol().qubit() == k) { // x_i + determinized number
            for (auto &out_ins : t.second) {
                std::set<StateVector> ins;
                for (auto in : out_ins.second) {
                    assert(in.size() == 2);
                    if (in.at(0) < num_of_states && in.at(1) < num_of_states) {
                        if (positive_has_value) {
                            in.at(0) += num_of_states;
                        } else {
                            in.at(1) += num_of_states;
                        }
                    }
                    ins.insert(in);
                }
                out_ins.second = ins;
            }
        }
    }
    remove_useless(); // otherwise, will out of memory
    auto end = std::chrono::steady_clock::now();
    branch_rest_time += end - start;
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::semi_determinize() {
    if (isTopdownDeterministic) return;
    TransitionMap transitions_copy = transitions;
    for (const auto &t : transitions_copy) {
        const SymbolTag &symbol_tag = t.first;
        if (symbol_tag.is_internal()) { // x_i not determinized yet
            assert(!symbol_tag.is_tagged()); // not determinized yet
            transitions.erase(symbol_tag); // modify
            int counter = 0;
            SymbolTag new_symbol;
            new_symbol.symbol() = symbol_tag.symbol();
            for (const auto &out_ins : t.second) {
                for (const auto &in : out_ins.second) {
                    new_symbol.tag().push_back(counter++);
                    transitions[new_symbol][out_ins.first].insert(in); // modify
                    new_symbol.tag().pop_back();
                }
            }
        }
    }
    // DO NOT reduce here.
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::semi_undeterminize() {
    if (isTopdownDeterministic) return;
    TransitionMap transitions_copy = transitions;
    for (const auto &t : transitions_copy) {
        const SymbolTag &symbol_tag = t.first;
        if (symbol_tag.is_internal()) { // pick all determinized x_i's
            assert(symbol_tag.is_tagged()); // determinized
            transitions.erase(symbol_tag); // modify
            for (const auto &in_out : t.second) {
                for (const auto &v : in_out.second)
                    transitions[symbol_tag.symbol()][in_out.first].insert(v); // modify
            }
        }
    }
    this->reduce();
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

#define construct_product_state_id(a, b, i) \
    State i; \
    if (overflow) { \
        auto it = stateOldToNew.find(std::make_pair(a, b)); \
        if (it == stateOldToNew.end()) { \
            i = stateOldToNew.size(); \
            stateOldToNew[std::make_pair(a, b)] = i; \
        } \
        else i = it->second; \
    } else i = a * o.stateNum + b;
template <typename Symbol>
AUTOQ::Automata<Symbol> AUTOQ::Automata<Symbol>::binary_operation(const Automata<Symbol> &o, bool add) {
    auto start = std::chrono::steady_clock::now();
    AUTOQ::Automata<Symbol> result;
    result.name = name;
    result.qubitNum = qubitNum;
    result.isTopdownDeterministic = isTopdownDeterministic; // IMPORTANT: Avoid missing copying new fields afterwards.

    std::map<std::pair<State, State>, State> stateOldToNew; // used only if overflow := true;
    bool overflow = (stateNum > std::numeric_limits<State>::max() / o.stateNum);
    if (!overflow) {}
        // result.finalStates.reserve(finalStates.size() * o.finalStates.size()); // TODO: Can we set the initial capacity?
    else
        throw std::overflow_error("[ERROR] The number of states after multiplication is too large.");

    for (const auto &fs1 : finalStates)
        for (const auto &fs2 : o.finalStates) {
            construct_product_state_id(fs1, fs2, i);
            result.finalStates.insert(i);
        }

    // We assume here transitions are ordered by symbols.
    // x_i are placed in the beginning, and leaves are placed in the end.
    // This traversal method is due to efficiency.
    std::vector<bool> previous_level_states2(stateNum * o.stateNum);
    std::vector<bool> previous_level_states(stateNum * o.stateNum);
    for (auto s : result.finalStates)
        previous_level_states[s] = true;
    std::vector<bool> next_level_states;
    auto it = transitions.begin();
    auto it2 = o.transitions.begin();
    for (; it != transitions.end(); it++) { // iterate over all internal transitions of T1
        if (it->first.is_leaf()) break; // internal
        if (it->first < it2->first) continue;
        while (it2 != o.transitions.end() && it->first > it2->first)
            it2++;
        if (it2 == o.transitions.end()) break;
        if (it->first < it2->first) continue;
        assert(it->first == it2->first); // Ensure T1's and T2's current transitions have the same symbol now.
        // Update previous_level_states.
        if (it != transitions.begin() && it->first.symbol().qubit() != std::prev(it)->first.symbol().qubit()) { // T1 changes level.
            previous_level_states = previous_level_states2;
            previous_level_states2 = std::vector<bool>(stateNum * o.stateNum);
        }
        // Update next_level_states.
        if (it == transitions.begin() || it->first.symbol().qubit() != std::prev(it)->first.symbol().qubit()) { // T1 goes into the new level.
            next_level_states = std::vector<bool>(stateNum * o.stateNum);
            auto it3 = it; // it3 indicates the next level of it.
            while (it3 != transitions.end() && it3->first.is_internal() && it3->first.symbol().qubit() == it->first.symbol().qubit())
                it3++;
            if (it3 == transitions.end()) {} // T1 has no leaf transitions?
            else if (it3->first.is_leaf()) { // The next level of T1 is leaf transitions.
                auto it4 = it2; // Initially it2 has the same symbol as it.
                while (it4 != o.transitions.end() && it4->first.is_internal())
                    it4++;
                auto it4i = it4;
                // We hope it4 currently points to the first leaf transition.
                // If it4 points to o.transitions.end(), then the following loop will not be executed.
                for (; it3 != transitions.end(); it3++) { // iterate over all leaf transitions of T1
                    assert(it3->first.is_leaf());
                    for (it4 = it4i; it4 != o.transitions.end(); it4++) { // iterate over all leaf transitions of T2
                        assert(it4->first.is_leaf());
                        for (const auto &kv1 : it3->second) { // iterate over all output states of it3
                            auto s1 = kv1.first;
                            for (const auto &kv2 : it4->second) { // iterate over all output states of it4
                                auto s2 = kv2.first;
                                construct_product_state_id(s1, s2, i);
                                next_level_states[i] = true; // collect all output state products of the next level
                            }
                        }
                    }
                }
            } else { // The next level of T1 is still internal transitions.
                int current_level = static_cast<int>(it3->first.symbol().qubit());
                auto it4 = it2; // Initially it2 has the same symbol as it.
                while (it4 != o.transitions.end() && it4->first.is_internal() && it4->first.symbol().qubit() == current_level)
                    it4++;
                // We hope it4 currently points to T2's first transition of the next level.
                // If it4 points to o.transitions.end(), then the following loop will not be executed.
                for (; it3->first.is_internal() && it3->first.symbol().qubit() == current_level; it3++) {
                    if (it3->first < it4->first) continue;
                    while (it4 != o.transitions.end() && it3->first > it4->first)
                        it4++;
                    if (it4 == o.transitions.end()) break;
                    if (it3->first < it4->first) continue;
                    assert(it3->first == it4->first);
                    // Ensure T1's and T2's current transitions have the same symbol now.
                    for (auto itt = it3->second.begin(); itt != it3->second.end(); itt++) { // all input-output pairs of it3
                        for (auto itt2 = it4->second.begin(); itt2 != it4->second.end(); itt2++) { // all input-output pairs of it4
                            auto s1 = itt->first; // all output states of it3
                            auto s2 = itt2->first; // all output states of it4
                            construct_product_state_id(s1, s2, i);
                            next_level_states[i] = true; // collect all output state products of the next level
                        }
                    }
                }
            }
        }
        std::map<State, std::set<StateVector>> m;
        for (auto itt = it->second.begin(); itt != it->second.end(); itt++) { // iterate over all output-input pairs of it
            for (auto itt2 = it2->second.begin(); itt2 != it2->second.end(); itt2++) { // iterate over all output-input pairs of it2
                construct_product_state_id(itt->first, itt2->first, newtop);
                if (previous_level_states[newtop]) {
                    std::set<StateVector> mm;
                    for (const auto &in : itt->second) { // all input vectors of itt
                        for (const auto &in2 : itt2->second) { // all input vectors of itt2
                            StateVector newin;
                            construct_product_state_id(in[0], in2[0], i);
                            if (!next_level_states[i]) continue;
                            newin.push_back(i); // construct product of T1's and T2's left input states
                            construct_product_state_id(in[1], in2[1], j);
                            if (!next_level_states[j]) continue;
                            newin.push_back(j); // construct product of T1's and T2's right input states
                            previous_level_states2[newin[0]] = true;
                            previous_level_states2[newin[1]] = true;
                            mm.insert(newin);
                        }
                    }
                    m.insert(std::make_pair(newtop, mm));
                }
            }
        }
        result.transitions.insert(make_pair(it->first, m));
        // assert(m.begin()->first.size() == 2);
    }
    previous_level_states = previous_level_states2;
    // We now advance it2 to T2's first leaf transition.
    while (it2 != o.transitions.end() && !it2->first.is_leaf())
        it2++;
    for (; it != transitions.end(); it++) {
        assert(it->first.is_leaf());
        for (auto it2t = it2; it2t != o.transitions.end(); it2t++) { // it2 as the new begin point.
            assert(it2t->first.is_leaf());
            Symbol symbol;
            if (add) symbol = it->first.symbol() + it2t->first.symbol();
            else symbol = it->first.symbol() - it2t->first.symbol();
            for (const auto &kv1 : it->second) {
                auto s1 = kv1.first;
                for (const auto &kv2 : it2t->second) {
                    auto s2 = kv2.first;
                    construct_product_state_id(s1, s2, i);
                    if (previous_level_states[i]) {
                        assert(it->first.tag() == it2t->first.tag()); // untagged
                        result.transitions[{symbol, it->first.tag()}][i].insert({{}});
                    }
                }
            }
        }
    }
    if (overflow)
        result.stateNum = stateOldToNew.size();
    else
        result.stateNum = stateNum * o.stateNum;
    result.remove_useless(true); // otherwise, will out of memory
    // Round several approximately equal floating points to the same value!
    #ifndef COMPLEX_FiveTuple
        result.fraction_simplification();
    #endif
    auto end = std::chrono::steady_clock::now();
    binop_time += end - start;
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
    return result;
}
template <typename Symbol>
AUTOQ::Automata<Symbol> Automata<Symbol>::operator+(const Automata &o) {
    return binary_operation(o, true);
}
template <typename Symbol>
AUTOQ::Automata<Symbol> Automata<Symbol>::operator-(const Automata &o) {
    return binary_operation(o, false);
}
template <typename Symbol>
AUTOQ::Automata<Symbol> AUTOQ::Automata<Symbol>::operator*(int c) {
    auto result = *this;
    std::vector<SymbolTag> to_be_removed;
    TransitionMap to_be_inserted;
    for (const auto &t : result.transitions) {
        SymbolTag symbol_tag = t.first;
        if (symbol_tag.is_leaf()) {
            to_be_removed.push_back(symbol_tag);
            symbol_tag.first.complex = symbol_tag.first.complex * c; // *= c;
            to_be_inserted[symbol_tag] = t.second;
        }
    }
    for (const auto &t : to_be_removed)
        result.transitions.erase(t);
    for (const auto &t : to_be_inserted)
        result.transitions.insert(t);
    // fraction_simplification();
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
    return result;
}

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::uniform(int n) {
    TreeAutomata aut;
    aut.name = "Uniform";
    aut.qubitNum = n;
    for (int level=1; level<=n; level++) {
        aut.transitions[{level}][level-1].insert({level, level});
    }
    aut.transitions[Concrete(Complex::Complex::One().divide_by_the_square_root_of_two(n))][n].insert({{}});
    aut.finalStates.insert(0);
    aut.stateNum = n+1;

    // aut.minimize();
    // aut.isTopdownDeterministic = true;
    return aut;
}

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::basis(int n) {
    TreeAutomata aut;
    aut.name = "Classical";
    aut.qubitNum = n;

    for (int level=1; level<=n; level++) {
        if (level >= 2)
            aut.transitions[{level}][2*level - 3].insert({2*level - 1, 2*level - 1});
        aut.transitions[{level}][2*level - 2].insert({2*level - 1, 2*level});
        aut.transitions[{level}][2*level - 2].insert({2*level, 2*level - 1});
    }
    aut.transitions[Concrete(Complex::Complex::One())][2*n].insert({{}});
    aut.transitions[Concrete(Complex::Complex::Zero())][2*n - 1].insert({{}});
    aut.finalStates.insert(0);
    aut.stateNum = 2*n + 1;

    // aut.minimize();
    return aut;
}

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::random(int n) {
    TreeAutomata aut;
    aut.name = "Random";
    aut.qubitNum = n;
    int pow_of_two = 1;
    State state_counter = 0;
    for (int level=1; level<=n; level++) {
        for (int i=0; i<pow_of_two; i++) {
            aut.transitions[{level}][state_counter].insert({state_counter*2+1, state_counter*2+2});
            state_counter++;
        }
        pow_of_two *= 2;
    }
    for (State i=state_counter; i<=state_counter*2; i++) {
        aut.transitions[Concrete(Complex::Complex::Rand())][i].insert({{}});
    }
    aut.finalStates.insert(0);
    aut.stateNum = state_counter*2 + 1;

    // aut.minimize();
    // aut.isTopdownDeterministic = true;
    return aut;
}

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::zero(int n) {
    /* Example of n = 6:
        Final States 0
        Transitions
        [1](2, 1) -> 0
        [2](3, 3) -> 1
        [2](4, 3) -> 2
        [3](5, 5) -> 3
        [3](6, 5) -> 4
        [4](7, 7) -> 5
        [4](8, 7) -> 6
        [5](9, 9) -> 7
        [5](10, 9) -> 8
        [6](11, 11) -> 9
        [6](12, 11) -> 10
        [0,0,0,0,0] -> 11
        [1,0,0,0,0] -> 12
    */
    TreeAutomata aut;
    aut.name = "Zero";
    aut.qubitNum = n;
    aut.finalStates.insert(0);
    aut.transitions[{1}][0].insert({2,1});
    for (int level=2; level<=n; level++) {
        aut.transitions[{level}][level*2-3].insert({level*2-1, level*2-1});
        aut.transitions[{level}][level*2-2].insert({level*2, level*2-1});
    }
    aut.transitions[Concrete(Complex::Complex::Zero())][n*2-1].insert({{}});
    aut.transitions[Concrete(Complex::Complex::One())][n*2].insert({{}});
    aut.stateNum = n*2 + 1;

    // aut.minimize();
    // aut.isTopdownDeterministic = true;
    return aut;
}

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::basis_zero_one_zero(int n) {
    TreeAutomata aut;
    assert(n >= 2);
    aut.name = "Classical_Zero_One_Zero";
    aut.qubitNum = n + (n+1) + (n>=3) * (n-1);

    for (int level=1; level<=n; level++) {
        if (level >= 2)
            aut.transitions[{level}][2*level - 3].insert({2*level - 1, 2*level - 1});
        aut.transitions[{level}][2*level - 2].insert({2*level - 1, 2*level});
        aut.transitions[{level}][2*level - 2].insert({2*level, 2*level - 1});
    }
    for (int level=1; level<=n; level++) {
        aut.transitions[{n + level}][2*n + 2*level-3].insert({2*n + 2*level-1, 2*n + 2*level-1});
        aut.transitions[{n + level}][2*n + 2*level-2].insert({2*n + 2*level, 2*n + 2*level-1});
    }
    aut.transitions[{n + (n+1)}][2*n + 2*(n+1)-3].insert({2*n + 2*(n+1)-1, 2*n + 2*(n+1)-1});
    aut.transitions[{n + (n+1)}][2*n + 2*(n+1)-2].insert({2*n + 2*(n+1)-1, 2*n + 2*(n+1)});
    if (n >= 3) {
        for (int level=n+2; level<=2*n; level++) {
            aut.transitions[{n + level}][2*n + 2*level-3].insert({2*n + 2*level-1, 2*n + 2*level-1});
            aut.transitions[{n + level}][2*n + 2*level-2].insert({2*n + 2*level, 2*n + 2*level-1});
        }
        aut.transitions[Concrete(Complex::Complex::One())][6*n].insert({{}});
        aut.transitions[Concrete(Complex::Complex::Zero())][6*n - 1].insert({{}});
        aut.stateNum = 6*n + 1;
    } else {
        assert(n == 2);
        aut.transitions[Concrete(Complex::Complex::One())][4*n + 2].insert({{}});
        aut.transitions[Concrete(Complex::Complex::Zero())][4*n + 1].insert({{}});
        aut.stateNum = 4*n + 3;
    }
	aut.finalStates.insert(0);
    return aut;
}

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::zero_zero_one_zero(int n) {
    TreeAutomata aut;
    assert(n >= 2);
    aut.name = "Zero_Zero_One_Zero";
    aut.qubitNum = n + (n+1) + (n>=3) * (n-1);

    aut.transitions[{1}][0].insert({2,1});
    for (int level=2; level<=n; level++) {
        aut.transitions[{level}][level*2-3].insert({level*2-1, level*2-1});
        aut.transitions[{level}][level*2-2].insert({level*2, level*2-1});
    }
    for (int level=1; level<=n; level++) {
        aut.transitions[{n + level}][2*n + 2*level-3].insert({2*n + 2*level-1, 2*n + 2*level-1});
        aut.transitions[{n + level}][2*n + 2*level-2].insert({2*n + 2*level, 2*n + 2*level-1});
    }
    aut.transitions[{n + (n+1)}][2*n + 2*(n+1)-3].insert({2*n + 2*(n+1)-1, 2*n + 2*(n+1)-1});
    aut.transitions[{n + (n+1)}][2*n + 2*(n+1)-2].insert({2*n + 2*(n+1)-1, 2*n + 2*(n+1)});
    if (n >= 3) {
        for (int level=n+2; level<=2*n; level++) {
            aut.transitions[{n + level}][2*n + 2*level-3].insert({2*n + 2*level-1, 2*n + 2*level-1});
            aut.transitions[{n + level}][2*n + 2*level-2].insert({2*n + 2*level, 2*n + 2*level-1});
        }
        aut.transitions[Concrete(Complex::Complex::One())][6*n].insert({{}});
        aut.transitions[Concrete(Complex::Complex::Zero())][6*n - 1].insert({{}});
        aut.stateNum = 6*n + 1;
    } else {
        assert(n == 2);
        aut.transitions[Concrete(Complex::Complex::One())][4*n + 2].insert({{}});
        aut.transitions[Concrete(Complex::Complex::Zero())][4*n + 1].insert({{}});
        aut.stateNum = 4*n + 3;
    }
	aut.finalStates.insert(0);
    // aut.isTopdownDeterministic = true;
    return aut;
}

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::zero_one_zero(int n) {
    TreeAutomata aut;
    assert(n >= 2);
    aut.name = "Zero_One_Zero";
    aut.qubitNum = (n+1) + (n>=3) * (n-1);

    aut.transitions[{1}][0].insert({2,1});
    for (int level=2; level<=n; level++) {
        aut.transitions[{level}][level*2-3].insert({level*2-1, level*2-1});
        aut.transitions[{level}][level*2-2].insert({level*2, level*2-1});
    }
    aut.transitions[{n+1}][2*n-1].insert({2*(n+1)-1, 2*(n+1)-1});
    aut.transitions[{n+1}][2*n].insert({2*(n+1)-1, 2*(n+1)});
    if (n >= 3) {
        for (int level=n+2; level<=2*n; level++) {
            aut.transitions[{level}][2*(level-1)-1].insert({2*level-1, 2*level-1});
            aut.transitions[{level}][2*(level-1)].insert({2*level, 2*level-1});
        }
        aut.transitions[Concrete(Complex::Complex::One())][4*n].insert({{}});
        aut.transitions[Concrete(Complex::Complex::Zero())][4*n - 1].insert({{}});
        aut.stateNum = 4*n + 1;
    } else {
        assert(n == 2);
        aut.transitions[Concrete(Complex::Complex::One())][2*n + 2].insert({{}});
        aut.transitions[Concrete(Complex::Complex::Zero())][2*n + 1].insert({{}});
        aut.stateNum = 2*n + 3;
    }
	aut.finalStates.insert(0);
    // aut.isTopdownDeterministic = true;
    return aut;
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::swap_forward(const int k) {
    if (isTopdownDeterministic) return;
    for (unsigned next_k=k+1; next_k<=qubitNum; next_k++) {
        std::map<State, std::vector<std::pair<SymbolTag, StateVector>>> svsv;
        for (const auto &t : transitions) {
            const auto &symbol_tag = t.first;
            if (symbol_tag.is_internal() && symbol_tag.symbol().qubit() == next_k) {
                assert(symbol_tag.tag().size() <= 1);
                for (const auto &out_ins : t.second) {
                    auto s = out_ins.first;
                    for (const auto &in : out_ins.second)
                        svsv[s].push_back(make_pair(symbol_tag, in));
                }
            }
        }
        std::vector<SymbolTag> to_be_removed2;
        TransitionMap to_be_removed;
        TransitionMap2 to_be_inserted;
        for (const auto &t : transitions) {
            const SymbolTag &symbol_tag = t.first;
            if (symbol_tag.is_internal() && symbol_tag.symbol().qubit() == k) {
                /***************************************/
                std::map<StateVector, State> in_s;
                for (const auto &out_ins : t.second) {
                    auto s = out_ins.first;
                    for (const auto &in : out_ins.second)
                        in_s[in] = s;
                }
                /***************************************/
                for (const auto &out_ins : t.second) {
                    auto s = out_ins.first;
                    for (const auto &in : out_ins.second) {
                        assert(in.size() == 2);
                        for (const auto &ssv1 : svsv[in[0]]) {
                            for (const auto &ssv2 : svsv[in[1]]) {
                                to_be_removed[ssv1.first][in[0]].insert(ssv1.second);
                                to_be_removed[ssv2.first][in[1]].insert(ssv2.second);
                                if (to_be_inserted[symbol_tag][{ssv1.second[0], ssv2.second[0]}].empty()) {
                                    auto it = in_s.find({ssv1.second[0], ssv2.second[0]});
                                    if (it == in_s.end())
                                        to_be_inserted[symbol_tag][{ssv1.second[0], ssv2.second[0]}].insert(stateNum++);
                                    else
                                        to_be_inserted[symbol_tag][{ssv1.second[0], ssv2.second[0]}].insert(it->second);
                                }
                                if (to_be_inserted[symbol_tag][{ssv1.second[1], ssv2.second[1]}].empty()) {
                                    auto it = in_s.find({ssv1.second[1], ssv2.second[1]});
                                    if (it == in_s.end())
                                        to_be_inserted[symbol_tag][{ssv1.second[1], ssv2.second[1]}].insert(stateNum++);
                                    else
                                        to_be_inserted[symbol_tag][{ssv1.second[1], ssv2.second[1]}].insert(it->second);
                                }
                                to_be_inserted[{Symbol(next_k), {ssv1.first.tag(0), ssv2.first.tag(0)}}][{*(to_be_inserted[symbol_tag][{ssv1.second[0], ssv2.second[0]}].begin()), *(to_be_inserted[symbol_tag][{ssv1.second[1], ssv2.second[1]}].begin())}].insert(s);
                            }
                        }
                    }
                }
                to_be_removed2.push_back(symbol_tag);
            }
        }
        for (const auto &v : to_be_removed2)
            transitions.erase(v);
        for (const auto &t : to_be_removed) {
            const SymbolTag &symbol_tag = t.first;
            for (const auto &out_ins : t.second) {
                auto s = out_ins.first;
                for (const auto &in : out_ins.second)
                    transitions[symbol_tag][s].erase(in);
                if (transitions[symbol_tag][s].empty())
                    transitions[symbol_tag].erase(s);
                if (transitions[symbol_tag].empty())
                    transitions.erase(symbol_tag);
            }
        }
        for (const auto &t : to_be_inserted) {
            const SymbolTag &symbol_tag = t.first;
            for (const auto &in_out : t.second) {
                for (const auto &s : in_out.second) {
                    transitions[symbol_tag][s].insert(in_out.first);
                }
            }
        }
        // DO NOT reduce here.
    }
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::swap_backward(const int k) {
    if (isTopdownDeterministic) return;

    /*************************************************/
    TransitionMap2 transitions2;
    for (const auto &t : transitions) {
        const auto &symbol_tag = t.first;
        for (const auto &out_ins : t.second) {
            auto s = out_ins.first;
            for (const auto &in : out_ins.second)
                transitions2[symbol_tag][in].insert(s);
        }
    }
    /*************************************************/

    for (int next_k=qubitNum; next_k>k; next_k--) {
        std::map<State, std::vector<std::pair<SymbolTag, StateVector>>> svsv;
        for (const auto &t : transitions2) {
            const auto &symbol_tag = t.first;
            const auto &in_outs = t.second;
            if (symbol_tag.is_internal() && symbol_tag.symbol().qubit() == k) {
                assert(symbol_tag.tag().size() == 1);
                for (const auto &in_out : in_outs) {
                    for (const auto &s : in_out.second)
                        svsv[s].push_back(make_pair(symbol_tag, in_out.first));
                }
            }
        }
        std::vector<SymbolTag> to_be_removed2;
        TransitionMap2 to_be_removed, to_be_inserted;
        for (const auto &t : transitions2) {
            const SymbolTag &symbol_tag = t.first;
            if (symbol_tag.is_internal() && symbol_tag.symbol().qubit() == next_k) {
                assert(symbol_tag.tag().size() == 2);
                for (const auto &in_out : t.second) {
                    assert(in_out.first.size() == 2);
                    for (const auto &ssv1 : svsv[in_out.first[0]]) {
                        for (const auto &ssv2 : svsv[in_out.first[1]]) {
                            if (ssv1.first == ssv2.first) {
                                to_be_removed[ssv1.first][ssv1.second].insert(in_out.first[0]);
                                to_be_removed[ssv2.first][ssv2.second].insert(in_out.first[1]);
                                SymbolTag t1 = {symbol_tag.symbol(), {symbol_tag.tag(0)}};
                                if (to_be_inserted[t1][{ssv1.second[0], ssv2.second[0]}].empty()) {
                                    if (transitions2[t1][{ssv1.second[0], ssv2.second[0]}].empty())
                                        to_be_inserted[t1][{ssv1.second[0], ssv2.second[0]}].insert(stateNum++);
                                    else
                                        to_be_inserted[t1][{ssv1.second[0], ssv2.second[0]}].insert(*(transitions2[t1][{ssv1.second[0], ssv2.second[0]}].begin()));
                                }
                                SymbolTag t2 = {symbol_tag.symbol(), {symbol_tag.tag(1)}};
                                if (to_be_inserted[t2][{ssv1.second[1], ssv2.second[1]}].empty()) {
                                    if (transitions2[t2][{ssv1.second[1], ssv2.second[1]}].empty())
                                        to_be_inserted[t2][{ssv1.second[1], ssv2.second[1]}].insert(stateNum++);
                                    else
                                        to_be_inserted[t2][{ssv1.second[1], ssv2.second[1]}].insert(*(transitions2[t2][{ssv1.second[1], ssv2.second[1]}].begin()));
                                }
                                assert(k == ssv1.first.symbol().qubit());
                                for (const auto &s : in_out.second)
                                    to_be_inserted[ssv1.first][{*(to_be_inserted[t1][{ssv1.second[0], ssv2.second[0]}].begin()), *(to_be_inserted[t2][{ssv1.second[1], ssv2.second[1]}].begin())}].insert(s);
                            }
                        }
                    }
                }
                to_be_removed2.push_back(symbol_tag);
            }
        }
        for (const auto &v : to_be_removed2)
            transitions2.erase(v);
        for (const auto &t : to_be_removed) {
            const SymbolTag &symbol_tag = t.first;
            for (const auto &in_out : t.second) {
                for (const auto &s : in_out.second)
                    transitions2[symbol_tag][in_out.first].erase(s);
                if (transitions2[symbol_tag][in_out.first].empty())
                    transitions2[symbol_tag].erase(in_out.first);
                if (transitions2[symbol_tag].empty())
                    transitions2.erase(symbol_tag);
            }
        }
        for (const auto &t : to_be_inserted) {
            const SymbolTag &symbol_tag = t.first;
            for (const auto &in_out : t.second) {
                for (const auto &s : in_out.second) {
                    transitions2[symbol_tag][in_out.first].insert(s);
                }
            }
        }
        // DO NOT reduce here.
    }
    /*************************************************/
    transitions.clear();
    for (const auto &t : transitions2) {
        const auto &symbol_tag = t.first;
        for (const auto &in_outs : t.second) {
            auto in = in_outs.first;
            for (const auto &s : in_outs.second)
                transitions[symbol_tag][s].insert(in);
        }
    }
    /*************************************************/
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::value_restriction(int k, bool branch) {
    auto start = std::chrono::steady_clock::now();
    swap_forward(k);
    for (auto &t : transitions) {
        const SymbolTag &symbol_tag = t.first;
        if (symbol_tag.is_internal() && symbol_tag.symbol().qubit() == k) {
            for (auto &out_ins : t.second) {
                std::set<StateVector> ins;
                for (auto in : out_ins.second) {
                    assert(in.size() == 2);
                    if (branch)
                        in.at(0) = in.at(1);
                    else
                        in.at(1) = in.at(0);
                    ins.insert(in);
                }
                out_ins.second = ins;
            }
        }
    }
    swap_backward(k);
    this->reduce();
    auto end = std::chrono::steady_clock::now();
    value_rest_time += end - start;
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::fraction_simplification() {
    std::vector<SymbolTag> to_be_removed;
    TransitionMap to_be_inserted;
    for (const auto &t : transitions) {
        const SymbolTag &s = t.first;
        if (s.is_leaf()) {
            SymbolTag symbol_tag = s;
            symbol_tag.symbol().fraction_simplification();
            if (t.first != symbol_tag) {
                to_be_removed.push_back(t.first);
                for (const auto &out_ins : t.second) {
                    const auto &out = out_ins.first;
                    for (const auto &in : out_ins.second) {
                        to_be_inserted[symbol_tag][out].insert(in);
                    }
                }
            }
        }
    }
    for (const auto &t : to_be_removed) transitions.erase(t);
    for (const auto &t : to_be_inserted) {
        for (const auto &kv : t.second)
            for (const auto &in : kv.second)
                transitions[t.first][kv.first].insert(in);
    }
    // remove_useless();
    // reduce();
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

/**************** Equivalence Checking ****************/
// namespace
// { // anonymous namespace
  std::string gpath_to_VATA = "";

  /** returns the path to AUTOQ executable */
  const std::string& get_vata_path()
  {
    // is it cached?
    if (!gpath_to_VATA.empty()) return gpath_to_VATA;

    // not cached, get it from ENV
    const char* path = std::getenv("VATA_PATH");
    if (nullptr == path) {
      throw std::runtime_error("[ERROR] The environment variable VATA_PATH is not found!");
    }

    gpath_to_VATA = path;
    return gpath_to_VATA;
  }

  const int MAX_ARG_STRLEN = 131070; // in fact is 131072 on the Internet

  /** checks inclusion of two TAs */
  template <typename Symbol>
  bool AUTOQ::Automata<Symbol>::check_inclusion(const std::string& lhsPath, const std::string& rhsPath)
  {
    std::string aux;
    AUTOQ::Util::ShellCmd(get_vata_path() + " incl " + lhsPath + " " + rhsPath, aux);
    return (aux == "1\n");
  }

  template <typename Symbol>
  bool AUTOQ::Automata<Symbol>::check_inclusion(const Automata<Symbol>& lhsPath, const std::string& rhsPath)
  {
    std::string aux;
    std::string aut1 = TimbukSerializer::Serialize(lhsPath);
    assert(aut1.length() <= MAX_ARG_STRLEN);
    AUTOQ::Util::ShellCmd(get_vata_path() + " incl2 '" + aut1 + "' " + rhsPath, aux);
    return (aux == "1\n");
  }

  template <typename Symbol>
  bool AUTOQ::Automata<Symbol>::check_inclusion(const std::string& lhsPath, const Automata<Symbol>& rhsPath)
  {
    std::string aux;
    std::string aut2 = TimbukSerializer::Serialize(rhsPath);
    assert(aut2.length() <= MAX_ARG_STRLEN);
    AUTOQ::Util::ShellCmd(get_vata_path() + " incl3 " + lhsPath + " '" + aut2 + "'", aux);
    return (aux == "1\n");
  }

  template <typename Symbol>
  bool AUTOQ::Automata<Symbol>::check_inclusion(const Automata<Symbol>& lhsPath, const Automata<Symbol>& rhsPath)
  {
    std::string input = TimbukSerializer::Serialize(lhsPath);
    std::vector<std::string> args{get_vata_path(), "incl4"};
    int length = input.length();
    for (int i=0; i<length; i+=MAX_ARG_STRLEN) {
        args.push_back(input.substr(i, MAX_ARG_STRLEN));
    }
    input = TimbukSerializer::Serialize(rhsPath);
    length = input.length();
    for (int i=0; i<length; i+=MAX_ARG_STRLEN) {
        args.push_back(input.substr(i, MAX_ARG_STRLEN));
    }
    std::string aux;
    if (!AUTOQ::Util::ShellCmd(args, aux)) {
        throw std::runtime_error("[ERROR] Failed to execute VATA.");
    }
    return (aux == "1\n");
  }

  /** checks language equivalence of two TAs */
  template <typename Symbol>
  bool AUTOQ::Automata<Symbol>::check_equal(const Automata<Symbol>& lhsPath, const Automata<Symbol>& rhsPath)
  {
    return check_inclusion(lhsPath, rhsPath) && check_inclusion(rhsPath, lhsPath);
  }

  template <>
  bool AUTOQ::TreeAutomata::check_equal_aut(
      AUTOQ::TreeAutomata lhs,
      AUTOQ::TreeAutomata rhs)
  {
	return check_equal(lhs, rhs);
  }
// } // anonymous namespace
/******************************************************/

// template <typename Symbol>
// void AUTOQ::Automata<Symbol>::sim_reduce()
// {
//   using State = typename Automata<Symbol>::State;
//   using DiscontBinaryRelOnStates = typename Util::DiscontBinaryRelation<State>;
//   using StateToStateMap = typename std::unordered_map<State, State>;

//   DiscontBinaryRelOnStates sim = compute_down_sim(*this);

//   // TODO: this is probably not optimal, we could probably get the mapping of
//   // states for collapsing in a faster way
//   sim.RestrictToSymmetric();       // sim is now an equivalence relation

//   StateToStateMap collapseMap;
//   sim.GetQuotientProjection(collapseMap);

//   // Automata old = *this;
//   reindex_aut_states(*this, collapseMap);

//   // if (!check_equal_aut(*this, old)) {
//   //   AUTOQ_DEBUG("wrong simulation result!");
//   //   AUTOQ_DEBUG("old: " + old.ToString());
//   //   AUTOQ_DEBUG("new: " + this->ToString());
//   //   AUTOQ_DEBUG("simulation: " + sim.ToString());
//   // }
// }

template <typename Symbol>
bool AUTOQ::Automata<Symbol>::execute(const char *filename) {
    std::string constraint;
    return execute(filename, constraint);
}
template <typename Symbol>
bool AUTOQ::Automata<Symbol>::execute(const char *filename, std::string &constraint) {
    bool verify = true;
    bool inGateDef = false;
    bool inWhileLoop = false;
    bool inIfBlock = false;
    bool inElseBlock = false;
    std::map<std::string, int> var_is_measure_what_qubit;
    std::string automatonI, constraintI, automatonQ, constraintQ, while_measurement_guard;
    AUTOQ::Automata<Symbol> I, measure_to_continue, measure_to_break, measure_to_else, result_after_if;
    std::ifstream qasm(filename);
    const std::regex digit("\\d+");
    const std::regex_iterator<std::string::iterator> END;
    if (!qasm.is_open()) throw std::runtime_error("[ERROR] Failed to open file " + std::string(filename) + ".");
    std::string line, previous_line;
    while (getline(qasm, line)) {
        line = AUTOQ::Util::trim(line);
        if (inGateDef) {
            if (line.find("}") != std::string::npos) {
                inGateDef = false;
            }
            continue; // simply ignore gate definitions
        }
        if (line.find("OPENQASM") == 0 || line.find("include ") == 0 || line.find("//") == 0 || line.find("bit") == 0) continue;
        if (line.find("qreg ") == 0 || line.find("qubit") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            while (it != END) {
                if (atoi(it->str().c_str()) != static_cast<int>(qubitNum))
                    throw std::runtime_error("[ERROR] The number of qubits in the automaton does not match the number of qubits in the circuit.");
                ++it;
            }
        } else if (line.find("x ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                X(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("y ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                Y(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("z ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                Z(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("h ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                H(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("s ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                S(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("sdg ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                Sdg(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("t ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                T(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("tdg ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                Tdg(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("rx(pi/2) ") == 0 || line.find("rx(pi / 2)") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                Rx(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("ry(pi/2) ") == 0 || line.find("ry(pi / 2)") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                Ry(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("cx ") == 0 || line.find("CX ") == 0 ) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            CNOT(pos[0], pos[1]);
        } else if (line.find("cz ") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            CZ(pos[0], pos[1]);
        } else if (line.find("ccustom ") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            CU(pos[0], pos[1]);
        } else if (line.find("ccx ") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            Toffoli(pos[0], pos[1], pos[2]);
        } else if (line.find("swap ") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            swap(pos[0], pos[1]);
        } else if (line.find("while") == 0) { // while (!result) { // loop-invariant.{spec|hsl}
            if (previous_line.find("measure") == std::string::npos)
                throw std::runtime_error("[ERROR] The while loop guard must be a measurement operator.");
            while_measurement_guard = previous_line;
            std::erase(while_measurement_guard, ' ');
            inWhileLoop = true;
            const std::regex varR("\\((.*)\\)");
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), varR);
            assert(it != END);
            std::string var = AUTOQ::Util::trim(it->str(1));
            bool negate = (var.at(0) == '!'); // whether the variable is negated
            if (negate)
                var = var.substr(1);
            int pos = var_is_measure_what_qubit[var];
            /********************************/
            const std::regex spec("// *(.*)");
            std::regex_iterator<std::string::iterator> it2(line.begin(), line.end(), spec);
            std::string dir = (std::filesystem::current_path() / filename).parent_path().string();
            I = AUTOQ::Parsing::TimbukParser<Symbol>::ReadAutomatonAndConstraint(dir + std::string("/") + it2->str(1), constraintI);
            /**************************************************************************************************************/
            // std::cout << "We first verify \"P ⊆ I\" here." << std::endl;
            // this->print_language("P:\n");
            // I.print_language("I:\n");
            this->remove_useless(); this->reduce(); I.remove_useless(); I.reduce();
            bool t = is_scaled_spec_satisfied(*this, constraint, I, constraintI);
            verify &= t;
            if (!t) AUTOQ_ERROR("[ERROR] P ⊈ I.");
            if (negate) {
                measure_to_continue = I.measure(pos, false);
                measure_to_break = I.measure(pos, true);
            } else { // while (measure ...
                measure_to_continue = I.measure(pos, true);
                measure_to_break = I.measure(pos, false);
            }
            *this = measure_to_continue;
        } else if (line.find("}") == 0) { // } // post.{spec|hsl}
            if (inWhileLoop) {
                inWhileLoop = false;
                std::erase(previous_line, ' ');
                if (while_measurement_guard != previous_line)
                    throw std::runtime_error("[ERROR] The while loop guard must be repeated at the end of the loop!");
                const std::regex spec("// *(.*)");
                std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), spec);
                std::string dir = (std::filesystem::current_path() / filename).parent_path().string();
                auto Q = AUTOQ::Parsing::TimbukParser<Symbol>::ReadAutomatonAndConstraint(dir + std::string("/") + it->str(1), constraintQ);
                /**************************************************************************************************************/
                measure_to_continue = *this; // is C(measure_to_continue)
                // std::cout << "Then we verify \"C(measure_to_continue) ⊆ I\" here." << std::endl;
                // measure_to_continue.print_language("C(measure_to_continue):\n");
                // I.print_language("I:\n");
                measure_to_continue.remove_useless(); measure_to_continue.reduce(); // I.remove_useless(); I.reduce();
                bool t = is_scaled_spec_satisfied(measure_to_continue, constraintI, I, constraintI);
                verify &= t;
                if (!t) AUTOQ_ERROR("[ERROR] C(measure_to_continue) ⊈ I.");
                // std::cout << "Then we verify \"measure_to_break ⊆ Q\" here." << std::endl;
                // measure_to_break.print_language("measure_to_break:\n");
                // Q.print_language("Q:\n");
                measure_to_break.remove_useless(); measure_to_break.reduce(); Q.remove_useless(); Q.reduce();
                t = is_scaled_spec_satisfied(measure_to_break, constraintI, Q, constraintQ);
                verify &= t;
                if (!t) AUTOQ_ERROR("[ERROR] measure_to_break ⊈ Q.");
                *this = Q; // Use this postcondition to execute the remaining circuit!
                constraint = constraintQ; // pass the postcondition's contraint to the main function for the later use!
                gateCount--; // retract the excess counting of the measurement operator in the while loop guard
            } else if (inIfBlock) {
                inIfBlock = false;
                result_after_if = *this; // this automaton is used to be merged with the result automaton after the "else" block if the "else" block is present.
                *this = this->Union(measure_to_else); // if the "else" block is absent, then that branch is simply the other measurement outcome.
            } else if (inElseBlock) {
                inElseBlock = false;
                *this = this->Union(result_after_if); // merge the else-branch result with the if-branch result
            }
        } else if (line.find("if") == 0) { // if (!result) {
            if (previous_line.find("measure") == std::string::npos)
                throw std::runtime_error("[ERROR] The if guard must be a measurement operator.");
            inIfBlock = true;
            const std::regex varR("\\((.*)\\)");
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), varR);
            assert(it != END);
            std::string var = AUTOQ::Util::trim(it->str(1));
            bool negate = (var.at(0) == '!'); // whether the variable is negated
            if (negate)
                var = var.substr(1);
            int pos = var_is_measure_what_qubit[var];
            if (negate) {
                measure_to_else = this->measure(pos, true);
                *this = this->measure(pos, false);
            } else { // if (measure ...
                measure_to_else = this->measure(pos, false);
                *this = this->measure(pos, true);
            }
        } else if (line.find("else") == 0) { // else {
            inElseBlock = true;
            *this = measure_to_else;
        } else if (line.find("gate ") == 0) {
            if (line.find("}") == std::string::npos) {
                inGateDef = true; // TODO: unsure if this is necessary
            }
        } else if (line.find("=") != std::string::npos && line.find("measure") != std::string::npos) {
            const std::regex m("([^ ]+) *= *measure.*\\[(\\d+)\\]"); // result = measure problem[4];
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), m);
            assert(it != END);
            std::string result = it->str(1);
            int pos = 1 + atoi(it->str(2).c_str());
            var_is_measure_what_qubit[result] = pos;
            // TODO: Actually, we should split the automaton here into two separate copies which
            // are produced from the measurement outcome of 0 and 1, respectively. However, we do
            // not do this for simplicity temporarily.
        } else if (line.length() > 0)
            throw std::runtime_error("[ERROR] unsupported gate: " + line + ".");
        // fraction_simplification();
        // print("\n" + line + "\n");
        // print_language(("\n" + line + "\n").c_str());
        if (line.length() > 0)
            previous_line = line;
    }
    qasm.close();
    return verify;
}

// std::string exec(const char* cmd) {
//     std::array<char, 128> buffer;
//     std::string result;
//     std::unique_ptr<FILE, decltype(&pclose)> pipe(popen(cmd, "r"), pclose);
//     if (!pipe) {
//         throw std::runtime_error("popen() failed!");
//     }
//     while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr) {
//         result += buffer.data();
//     }
//     return result;
// }
#include <chrono>
using namespace std;
std::string toString2(std::chrono::steady_clock::duration tp) {
    using namespace std;
    using namespace std::chrono;
    nanoseconds ns = duration_cast<nanoseconds>(tp);
    typedef duration<int, ratio<86400>> days;
    std::stringstream ss;
    char fill = ss.fill();
    ss.fill('0');
    auto d = duration_cast<days>(ns);
    ns -= d;
    auto h = duration_cast<hours>(ns);
    ns -= h;
    auto m = duration_cast<minutes>(ns);
    ns -= m;
    auto s = duration_cast<seconds>(ns);
    ns -= s;
    auto ms = duration_cast<milliseconds>(ns);
    // auto s = duration<float, std::ratio<1, 1>>(ns);
    if (d.count() > 0 || h.count() > 0)
        ss << d.count() << 'd' << h.count() << 'h' << m.count() << 'm' << s.count() << 's';
    else if (m.count() == 0 && s.count() < 10) {
        ss << s.count() << '.' << ms.count() / 100 << "s";
    } else {
        if (m.count() > 0) ss << m.count() << 'm';
        ss << s.count() << 's';// << " & ";
    }
    ss.fill(fill);
    return ss.str();
}
bool AUTOQ::check_validity(Constraint C, const PredicateAutomata::Symbol &ps, const SymbolicAutomata::Symbol &te) {
    std::string str(ps);
    auto regToExpr = C.to_exprs(te);
    for (const auto &kv : regToExpr) // example: z3 <(echo '(declare-fun x () Int)(declare-fun z () Int)(assert (= z (+ x 3)))(check-sat)')
        str = std::regex_replace(str, std::regex(kv.first), kv.second);
    // std::cout << std::string(C) + "(assert (not " + str + "))(check-sat)\n";
    std::string smt_input = "bash -c \"z3 <(echo '" + std::string(C) + "(assert (not " + str + "))(check-sat)')\"";
    // auto startSim = chrono::steady_clock::now();
    ShellCmd(smt_input, str);
    // std::cout << smt_input << "\n";
    // std::cout << str << "\n";
    // auto durationSim = chrono::steady_clock::now() - startSim;
    // std::cout << toString2(durationSim) << "\n";
    if (str == "unsat\n") return true;
    else if (str == "sat\n") return false;
    else {
        std::cout << smt_input << "\n";
        std::cout << str << "-\n";
        throw std::runtime_error("[ERROR] The solver Z3 did not correctly return SAT or UNSAT.\nIt's probably because the specification automaton is NOT a predicate automaton.");
    }
}
bool AUTOQ::call_SMT_solver(const string &C, const string &str) {
    std::string result;
    // std::string str(ps);
    // auto regToExpr = C.to_exprs(te);
    // for (const auto &kv : regToExpr) // example: z3 <(echo '(declare-fun x () Int)(declare-fun z () Int)(assert (= z (+ x 3)))(check-sat)')
    //     str = std::regex_replace(str, std::regex(kv.first), kv.second);
    // std::cout << std::string(C) + "(assert (not " + str + "))(check-sat)\n";
    std::string smt_input = "bash -c \"z3 <(echo '" + C + "(assert " + str + ")(check-sat)')\"";
    // auto start = chrono::steady_clock::now();
    // std::cout << smt_input << "\n";
    ShellCmd(smt_input, result);
    // std::cout << result << "\n";
    // auto duration = chrono::steady_clock::now() - start;
    // std::cout << toString2(duration) << "\n";
    if (result == "unsat\n") return false;
    else if (result == "sat\n") return true;
    else {
        std::cout << smt_input << "\n";
        std::cout << result << "-\n";
        throw std::runtime_error("[ERROR] The solver Z3 did not correctly return SAT or UNSAT.");
    }
}
bool AUTOQ::is_spec_satisfied(const Constraint &C, const SymbolicAutomata &Ae, const PredicateAutomata &As) {
    using State = SymbolicAutomata::State;
    using StateSet = SymbolicAutomata::StateSet;
    using StateVector = SymbolicAutomata::StateVector;
    StateSet As_finalStates(As.finalStates.begin(), As.finalStates.end());
    std::vector<std::pair<State, StateSet>> processed; // ← ∅;
    std::queue<std::pair<State, StateSet>> worklist;
    for (const auto &te : Ae.transitions) {
        if (te.first.is_leaf()) {
            StateSet ss;
            for (const auto &out_ins : te.second) {
                // if (out_ins.second.contains({})) {
                    ss.insert(out_ins.first);
                // }
            }
            for (const auto &qe: ss) {
                StateSet Us;
                for (const auto &ps : As.transitions) {
                    if (ps.first.is_leaf()) {
                        if (check_validity(C, ps.first.symbol(), te.first.symbol())) { // C ⇒ ps(te)
                            for (const auto &kv : ps.second) {
                                // if (kv.second.contains({}))
                                    Us.insert(kv.first);
                            }
                        }
                    }
                } // compute Us above!
                worklist.push({qe, Us});
            }
        }
    } // antichainize Worklist
    while (!worklist.empty()) {
        auto qeUs = worklist.front();
        worklist.pop();
        if (std::find(processed.begin(), processed.end(), qeUs) == processed.end()) { // not found
            processed.push_back(qeUs);
            for (const auto &te : Ae.transitions) {
                if (te.first.is_internal()) {
                    const auto &alpha = te.first;
                    auto qeUs1 = qeUs;
                    for (auto qeUs2 : processed) {
                        bool flip = false;
                        do {
                            // Assume Ae and As have the same internal symbols!
                            StateSet Hs;
                            std::map<StateVector, StateSet> svss;
                            for (const auto &out_ins : As.transitions.at({AUTOQ::Symbol::Predicate(alpha.symbol().complex.at(Complex::Complex::One()).at("1")), {}})) {
                                for (const auto &in : out_ins.second) {
                                    svss[in].insert(out_ins.first);
                                }
                            }
                            for (const auto &in_out : svss) {
                                assert(in_out.first.size() == 2);
                                if (qeUs1.second.find(in_out.first[0]) != qeUs1.second.end()
                                    && qeUs2.second.find(in_out.first[1]) != qeUs2.second.end()) {
                                        Hs.insert(in_out.second.begin(), in_out.second.end());
                                    }
                            } // compute Hs above!
                            StateVector output;
                            std::set_intersection(Hs.begin(), Hs.end(), As_finalStates.begin(), As_finalStates.end(), std::back_inserter(output));
                            // output.resize(it - output.begin());
                            bool Hs_Rs_no_intersection = output.empty();
                            // check the above boolean value!
                            StateSet ss;
                            for (const auto &out_ins : te.second) {
                                if (out_ins.second.contains({qeUs1.first, qeUs2.first})) {
                                    ss.insert(out_ins.first);
                                }
                            }
                            for (const auto &q : ss) { // He
                                auto qHs = std::make_pair(q, Hs);
                                if (std::find(processed.begin(), processed.end(), qHs) == processed.end()) { // not found
                                    if (std::find(Ae.finalStates.begin(), Ae.finalStates.end(), q) != Ae.finalStates.end()
                                        && Hs_Rs_no_intersection) {
                                        return false;
                                    }
                                    worklist.push(qHs);
                                    // antichainize Worklist and Processed
                                }
                            }
                            // perform swap
                            std::swap(qeUs1, qeUs2);
                            flip = !flip;
                        } while (flip);
                    }
                }
            }
        }
    }
    return true;
}

#define MIN
struct PairComparator {
    bool operator()(const std::pair<TreeAutomata::State, std::pair<Complex::Complex, Complex::Complex>> &lhs, const std::pair<TreeAutomata::State, std::pair<Complex::Complex, Complex::Complex>> &rhs) const {
        auto lhsS = lhs.first;
        auto rhsS = rhs.first;
        auto lhsC = lhs.second;
        auto rhsC = rhs.second;
        return !(lhsS == rhsS && (
            (lhsC.first.isZero() && rhsC.first.isZero()) ||
            (!lhsC.first.isZero() && !rhsC.first.isZero() && (lhsC.first * rhsC.second).valueEqual(lhsC.second * rhsC.first))
        ));
    }
};
bool AUTOQ::is_scaled_spec_satisfied(const TreeAutomata &R, std::string constraintR, const TreeAutomata &Q, std::string constraintQ) {
    return is_scaled_spec_satisfied(R, Q);
}
bool AUTOQ::is_scaled_spec_satisfied(const TreeAutomata &R, const TreeAutomata &Q) {
    using State = TreeAutomata::State;
    using StateSet = TreeAutomata::StateSet;
    using StateScaleSet = std::set<std::pair<State, std::pair<Complex::Complex, Complex::Complex>>, PairComparator>;
    StateSet As_finalStates(Q.finalStates.begin(), Q.finalStates.end());
    std::map<State, std::set<StateScaleSet>> processed; // Line 1: ← ∅;
    std::map<State, std::set<StateScaleSet>> worklist;

    TreeAutomata::TransitionMap2 R_transitions;
    for (const auto &t : R.transitions) {
        const auto &symbol_tag = t.first;
        for (const auto &out_ins : t.second) {
            auto s = out_ins.first;
            for (const auto &in : out_ins.second)
                R_transitions[symbol_tag][in].insert(s);
        }
    }
    TreeAutomata::TransitionMap2 Q_transitions;
    for (const auto &t : Q.transitions) {
        const auto &symbol_tag = t.first;
        for (const auto &out_ins : t.second) {
            auto s = out_ins.first;
            for (const auto &in : out_ins.second)
                Q_transitions[symbol_tag][in].insert(s);
        }
    }

    /************************************/
    // Line 2-4: Construct the initial worklist!
    for (const auto &tr : R_transitions) {
        if (tr.first.is_leaf()) {
            const auto &vr = tr.first;
            const auto &cr = vr.symbol().complex;
            for (const auto &sr : tr.second.at({})) {
                StateScaleSet Uq;
                if (cr.isZero()) {
                    for (const auto &tq : Q_transitions) {
                        if (tq.first.is_leaf()) {
                            const auto &vq = tq.first;
                            const auto &cq = vq.symbol().complex;
                            if (cq.isZero()) {
                                for (const auto &uq : tq.second.at({})) {
                                    Uq.insert({uq, {cr, cq}}); // here 0 := ?
                                }
                            }
                        }
                    }
                } else { // cr is not zero
                    for (const auto &tq : Q_transitions) {
                        if (tq.first.is_leaf()) {
                            const auto &vq = tq.first;
                            const auto &cq = vq.symbol().complex;
                            if (!cq.isZero()) {
                                for (const auto &uq : tq.second.at({})) {
                                    Uq.insert({uq, {cq, cr}});
                                }
                            }
                        }
                    }
                }
                #ifdef MIN
                auto copy = worklist[sr]; // Min{...}
                for (const auto &t : copy) {
                    if (std::includes(t.begin(), t.end(), Uq.begin(), Uq.end()))
                        worklist[sr].erase(t);
                }
                bool cancel = false;
                for (const auto &t : worklist[sr]) {
                    if (std::includes(Uq.begin(), Uq.end(), t.begin(), t.end())) {
                        cancel = true;
                        break;
                    }
                }
                if (!cancel)
                #endif
                    worklist[sr].insert(Uq);
            }
        }
    }
    /************************************/
    while (!worklist.empty()) { // Line 5
        /*********************************************/
        // Line 6
        auto it = worklist.begin(); // const auto &it ?
        if (it->second.empty()) {
            worklist.erase(it);
            continue;
        }
        auto sr = it->first;
        auto Uq = *(it->second.begin());
        it->second.erase(it->second.begin());
        /*********************************************/
        // Line 7
        if (R.finalStates.contains(sr)) {
            StateSet ss;
            for (const auto &uq_c : Uq) {
                auto uq = uq_c.first;
                ss.insert(uq);
            }
            std::set<int> intersection; // Create a set to store the intersection
            std::set_intersection( // Use set_intersection to find the common elements
                ss.begin(), ss.end(),
                Q.finalStates.begin(), Q.finalStates.end(),
                std::inserter(intersection, intersection.begin())
            );
            if (intersection.empty()) { // Check if the intersection is empty
                return false;
            }
        }
        /*********************************************/
        // Line 8
        #ifdef MIN
        auto copy = processed[sr]; // Min{...}
        for (const auto &t : copy) {
            if (std::includes(t.begin(), t.end(), Uq.begin(), Uq.end()))
                processed[sr].erase(t);
        }
        bool cancel = false;
        for (const auto &t : processed[sr]) {
            if (std::includes(Uq.begin(), Uq.end(), t.begin(), t.end())) {
                cancel = true;
                break;
            }
        }
        if (!cancel)
        #endif
            processed[sr].insert(Uq);
        // std::cout << AUTOQ::Util::Convert::ToString(processed) << "\n";
        /*********************************************/
        // Line 10
        auto sr1 = sr;
        const auto &Uq1 = Uq;
        for (const auto &kv : processed) {
            auto sr2 = kv.first;
            for (const auto &Uq2 : kv.second) {
                for (const auto &tr : R_transitions) {
                    const auto &alpha = tr.first;
                    /*********************************************/
                    // Line 11
                    auto Hr_ptr = tr.second.find({sr1, sr2});
                    if (Hr_ptr == tr.second.end()) continue;
                    StateSet Hr = Hr_ptr->second;
                    if (Hr.empty()) continue;
                    /*********************************************/
                    StateScaleSet Uq_; // Line 12
                    /*********************************************/
                    // Line 13
                    for (const auto &kv1 : Uq1) {
                        const auto &sq1 = kv1.first;
                        const auto &r1 = kv1.second;
                        for (const auto &kv2 : Uq2) {
                            const auto &sq2 = kv2.first;
                            const auto &r2 = kv2.second;
                            /*********************************************/
                            // Line 15
                            StateSet sqSet;
                            auto it = Q_transitions.find(alpha);
                            if (it != Q_transitions.end()) {
                                auto ptr = it->second.find({sq1, sq2});
                                if (ptr == it->second.end()) continue;
                                sqSet = ptr->second;
                            }
                            if (sqSet.empty()) continue;
                            // Line 14
                            if (!(r1.first * r2.second).valueEqual(r1.second * r2.first) && !r1.first.isZero() && !r2.first.isZero()) {
                                continue;
                            }
                            /*********************************************/
                            // Line 16
                            auto c = r1.first.isZero() ? r2 : r1;
                            for (const auto &sq : sqSet) {
                                Uq_.insert(std::make_pair(sq, c));
                            }
                            /*********************************************/
                        }
                    }
                    /*********************************************/
                    // Line 17-18
                    for (const auto &sr_ : Hr) {
                        if (!processed[sr_].contains(Uq_) && !worklist[sr_].contains(Uq_)) {
                            #ifdef MIN
                            auto copy = worklist[sr_]; // Min{...}
                            for (const auto &t : copy) {
                                if (std::includes(t.begin(), t.end(), Uq_.begin(), Uq_.end()))
                                    worklist[sr_].erase(t);
                            }
                            bool cancel = false;
                            for (const auto &t : worklist[sr_]) {
                                if (std::includes(Uq_.begin(), Uq_.end(), t.begin(), t.end())) {
                                    cancel = true;
                                    break;
                                }
                            }
                            if (!cancel)
                            #endif
                                worklist[sr_].insert(Uq_);
                        }
                    }
                    /*********************************************/
                }
            }
        }
        auto sr2 = sr;
        const auto &Uq2 = Uq;
        for (const auto &kv : processed) {
            auto sr1 = kv.first;
            for (const auto &Uq1 : kv.second) {
                if (sr1 == sr2 && Uq1 == Uq2) continue;
                for (const auto &tr : R_transitions) {
                    const auto &alpha = tr.first;
                    /*********************************************/
                    // Line 11
                    auto Hr_ptr = tr.second.find({sr1, sr2});
                    if (Hr_ptr == tr.second.end()) continue;
                    StateSet Hr = Hr_ptr->second;
                    if (Hr.empty()) continue;
                    /*********************************************/
                    StateScaleSet Uq_; // Line 12
                    /*********************************************/
                    // Line 13
                    for (const auto &kv1 : Uq1) {
                        const auto &sq1 = kv1.first;
                        const auto &r1 = kv1.second;
                        for (const auto &kv2 : Uq2) {
                            const auto &sq2 = kv2.first;
                            const auto &r2 = kv2.second;
                            /*********************************************/
                            // Line 15
                            StateSet sqSet;
                            auto it = Q_transitions.find(alpha);
                            if (it != Q_transitions.end()) {
                                auto ptr = it->second.find({sq1, sq2});
                                if (ptr == it->second.end()) continue;
                                sqSet = ptr->second;
                            }
                            if (sqSet.empty()) continue;
                            // Line 14
                            if (!(r1.first * r2.second).valueEqual(r1.second * r2.first) && !r1.first.isZero() && !r2.first.isZero()) {
                                continue;
                            }
                            /*********************************************/
                            // Line 16
                            auto c = r1.first.isZero() ? r2 : r1;
                            for (const auto &sq : sqSet) {
                                Uq_.insert(std::make_pair(sq, c));
                            }
                            /*********************************************/
                        }
                    }
                    /*********************************************/
                    // Line 17-18
                    for (const auto &sr_ : Hr) {
                        if (!processed[sr_].contains(Uq_) && !worklist[sr_].contains(Uq_)) {
                            #ifdef MIN
                            auto copy = worklist[sr_]; // Min{...}
                            for (const auto &t : copy) {
                                if (std::includes(t.begin(), t.end(), Uq_.begin(), Uq_.end()))
                                    worklist[sr_].erase(t);
                            }
                            bool cancel = false;
                            for (const auto &t : worklist[sr_]) {
                                if (std::includes(Uq_.begin(), Uq_.end(), t.begin(), t.end())) {
                                    cancel = true;
                                    break;
                                }
                            }
                            if (!cancel)
                            #endif
                                worklist[sr_].insert(Uq_);
                        }
                    }
                    /*********************************************/
                }
            }
        }
    }
    return true;
}
bool AUTOQ::is_scaled_spec_satisfied(SymbolicAutomata R, std::string constraintR, SymbolicAutomata Q, std::string constraintQ) {
    if (R.StrictlyEqual(Q) && constraintR == constraintQ) return true;
    auto start = chrono::steady_clock::now();

    using State = SymbolicAutomata::State;
    using StateSet = SymbolicAutomata::StateSet;
    using SymbolicComplex = AUTOQ::Symbol::SymbolicComplex;
    using StateScaleSet = std::set<std::pair<State, unsigned>>; // int <-> std::pair<SymbolicComplex, SymbolicComplex>
    StateSet As_finalStates(Q.finalStates.begin(), Q.finalStates.end());
    std::map<State, std::set<StateScaleSet>> processed; // Line 1: ← ∅;
    std::map<State, std::set<StateScaleSet>> worklist;

    const std::regex_iterator<std::string::iterator> END;
    const std::regex var("\\(declare-fun[ ]+([^ ]+)[ ]+\\(\\)"); // (declare-fun v1 () Real)
    /*********************************************************/
    // Rename the variables in R's transitions and constraints!
    std::regex_iterator<std::string::iterator> it(constraintR.begin(), constraintR.end(), var);
    std::set<std::string> varsR, varsQ;
    while (it != END) {
        varsR.insert(it->str(1));
        // std::cout << it->str(1) << "\n";
        ++it;
    }
    auto transitions2 = R.transitions;
    for (const auto &tr : transitions2) {
        if (tr.first.symbol().is_leaf()) {
            AUTOQ::Symbol::SymbolicComplex complex_new;
            for (const auto &c_lc : tr.first.symbol().complex) { // std::map<Complex::Complex, AUTOQ::Symbol::linear_combination>
                auto lc = c_lc.second;
                AUTOQ::Symbol::linear_combination lc_new;
                for (const auto &v_i : lc) { // std::map<std::string, boost::multiprecision::cpp_int>
                    if (varsR.contains(v_i.first))
                        lc_new[v_i.first + "_R"] = v_i.second;
                    else
                        lc_new[v_i.first] = v_i.second;
                }
                complex_new[c_lc.first] = lc_new;
            }
            R.transitions.erase(tr.first.symbol());
            R.transitions[AUTOQ::Symbol::Symbolic(complex_new)] = tr.second;
        }
    }
    for (const auto &var : varsR)
        constraintR = std::regex_replace(constraintR, std::regex("(\\b" + var + "\\b)"), var + "_R");
    /*********************************************************/
    // Rename the variables in Q's transitions and constraints!
    std::regex_iterator<std::string::iterator> it2(constraintQ.begin(), constraintQ.end(), var);
    while (it2 != END) {
        varsQ.insert(it2->str(1));
        // std::cout << it2->str(1) << "\n";
        ++it2;
    }
    transitions2 = Q.transitions;
    for (const auto &tr : transitions2) {
        if (tr.first.symbol().is_leaf()) {
            AUTOQ::Symbol::SymbolicComplex complex_new;
            for (const auto &c_lc : tr.first.symbol().complex) { // std::map<Complex::Complex, AUTOQ::Symbol::linear_combination>
                auto lc = c_lc.second;
                AUTOQ::Symbol::linear_combination lc_new;
                for (const auto &v_i : lc) { // std::map<std::string, boost::multiprecision::cpp_int>
                    if (varsQ.contains(v_i.first))
                        lc_new[v_i.first + "_Q"] = v_i.second;
                    else
                        lc_new[v_i.first] = v_i.second;
                }
                complex_new[c_lc.first] = lc_new;
            }
            Q.transitions.erase(tr.first.symbol());
            Q.transitions[AUTOQ::Symbol::Symbolic(complex_new)] = tr.second;
        }
    }
    for (const auto &var : varsQ)
        constraintQ = std::regex_replace(constraintQ, std::regex("(\\b" + var + "\\b)"), var + "_Q");
    /*********************************************************/

    SymbolicAutomata::TransitionMap2 R_transitions;
    for (const auto &t : R.transitions) {
        const auto &symbol_tag = t.first;
        for (const auto &out_ins : t.second) {
            auto s = out_ins.first;
            for (const auto &in : out_ins.second)
                R_transitions[symbol_tag][in].insert(s);
        }
    }
    SymbolicAutomata::TransitionMap2 Q_transitions;
    for (const auto &t : Q.transitions) {
        const auto &symbol_tag = t.first;
        for (const auto &out_ins : t.second) {
            auto s = out_ins.first;
            for (const auto &in : out_ins.second)
                Q_transitions[symbol_tag][in].insert(s);
        }
    }


    /************************************/
    // Line 2-4: Construct the initial worklist!
    std::map<std::pair<SymbolicComplex, SymbolicComplex>, int> ratioInverseMap;
    std::vector<std::pair<SymbolicComplex, SymbolicComplex>> ratioMap;
    for (const auto &tr : R_transitions) {
        if (tr.first.is_leaf()) {
            const auto &vr = tr.first;
            const auto &cr = vr.symbol().complex;
            for (const auto &sr : tr.second.at({})) {
                StateScaleSet Uq;
                for (const auto &tq : Q_transitions) {
                    if (tq.first.is_leaf()) {
                        const auto &vq = tq.first;
                        const auto &cq = vq.symbol().complex;
                        // std::cout << cq.realToSMT() << "\n";
                        // std::cout << cq.imagToSMT() << "\n";
                        // std::cout << cr.realToSMT() << "\n";
                        // std::cout << cr.imagToSMT() << "\n";
                        if (call_SMT_solver(constraintR + constraintQ,
                                "(and (= " + cq.realToSMT() + " 0)(= " + cq.imagToSMT() + " 0)(= " + cr.realToSMT() + " 0)(= " + cr.imagToSMT() + " 0))") // cq == 0 && cr == 0
                         || call_SMT_solver(constraintR + constraintQ,
                                "(and (or (not (= " + cq.realToSMT() + " 0))(not (= " + cq.imagToSMT() + " 0)))(or (not (= " + cr.realToSMT() + " 0))(not (= " + cr.imagToSMT() + " 0))))") // cq != 0 && cr != 0
                        ) {
                            for (const auto &uq : tq.second.at({})) {
                                auto it = ratioInverseMap.find({cq, cr});
                                if (it == ratioInverseMap.end()) {
                                    ratioInverseMap[{cq, cr}] = ratioInverseMap.size();
                                    it = ratioInverseMap.find({cq, cr});
                                    ratioMap.push_back({cq, cr});
                                }
                                Uq.insert({uq, 1 << (it->second)});
                            }
                        }
                    }
                }
                #ifdef MIN
                auto copy = worklist[sr]; // Min{...}
                for (const auto &t : copy) {
                    if (std::includes(t.begin(), t.end(), Uq.begin(), Uq.end()))
                        worklist[sr].erase(t);
                }
                bool cancel = false;
                for (const auto &t : worklist[sr]) {
                    if (std::includes(Uq.begin(), Uq.end(), t.begin(), t.end())) {
                        cancel = true;
                        break;
                    }
                }
                if (!cancel)
                #endif
                    worklist[sr].insert(Uq);
            }
        }
    }
    // std::cout << "Worklist: " << AUTOQ::Util::Convert::ToString(worklist) << "\n";
    /************************************/
    // std::cout << AUTOQ::Util::Convert::ToString(ratioMap) << std::endl;
    // std::cout << AUTOQ::Util::Convert::ToString(ratioInverseMap) << std::endl;

    // Pre-compute satisfiabilities for all possible combinations of ratios for efficiency!
    std::vector<int> ratioIDs(ratioMap.size());
    std::iota(ratioIDs.begin(), ratioIDs.end(), 0);
    // std::cout << AUTOQ::Util::Convert::ToString(ratioIDs) << std::endl;
    std::vector<bool> DP(1 << ratioIDs.size()); // dynamic programming
    std::vector<bool> DP_enable(1 << ratioIDs.size());

    /************************************/
    while (!worklist.empty()) { // Line 5
        /*********************************************/
        // Line 6
        auto it = worklist.begin(); // const auto &it ?
        if (it->second.empty()) {
            worklist.erase(it);
            continue;
        }
        auto sr = it->first;
        auto Uq = *(it->second.begin());
        it->second.erase(it->second.begin());
        /*********************************************/
        // Line 7
        if (R.finalStates.contains(sr)) {
            StateSet ss;
            for (const auto &uq_c : Uq) {
                auto uq = uq_c.first;
                ss.insert(uq);
            }
            std::set<int> intersection; // Create a set to store the intersection
            std::set_intersection( // Use set_intersection to find the common elements
                ss.begin(), ss.end(),
                Q.finalStates.begin(), Q.finalStates.end(),
                std::inserter(intersection, intersection.begin())
            );
            if (intersection.empty()) { // Check if the intersection is empty
                auto duration = chrono::steady_clock::now() - start;
                std::cout << toString2(duration) << "\n";
                return false;
            }
        }
        /*********************************************/
        // Line 8
        #ifdef MIN
        auto copy = processed[sr]; // Min{...}
        for (const auto &t : copy) {
            if (std::includes(t.begin(), t.end(), Uq.begin(), Uq.end()))
                processed[sr].erase(t);
        }
        bool cancel = false;
        for (const auto &t : processed[sr]) {
            if (std::includes(Uq.begin(), Uq.end(), t.begin(), t.end())) {
                cancel = true;
                break;
            }
        }
        if (!cancel)
        #endif
            processed[sr].insert(Uq);
        // std::cout << AUTOQ::Util::Convert::ToString(processed) << "\n";
        /*********************************************/
        // Line 10
        auto sr1 = sr;
        const auto &Uq1 = Uq;
        for (const auto &kv : processed) {
            auto sr2 = kv.first;
            for (const auto &Uq2 : kv.second) {
                for (const auto &tr : R_transitions) {
                    const auto &alpha = tr.first;
                    /*********************************************/
                    // Line 11
                    auto Hr_ptr = tr.second.find({sr1, sr2});
                    if (Hr_ptr == tr.second.end()) continue;
                    StateSet Hr = Hr_ptr->second;
                    if (Hr.empty()) continue;
                    /*********************************************/
                    StateScaleSet Uq_; // Line 12
                    /*********************************************/
                    // Line 13
                    for (const auto &kv1 : Uq1) {
                        const auto &sq1 = kv1.first;
                        const auto &c1_set = kv1.second;
                        assert(c1_set > 0);
                        for (const auto &kv2 : Uq2) {
                            const auto &sq2 = kv2.first;
                            const auto &c2_set = kv2.second;
                            assert(c2_set > 0);
                            /*********************************************/
                            // Line 15
                            StateSet sqSet;
                            auto it = Q_transitions.find(alpha);
                            if (it != Q_transitions.end()) {
                                auto ptr = it->second.find({sq1, sq2});
                                if (ptr == it->second.end()) continue;
                                sqSet = ptr->second;
                            }
                            if (sqSet.empty()) continue;
                            // Line 14
                            unsigned unionSet = c1_set | c2_set;
                            // std::vector<int> unionVector(unionSet.begin(), unionSet.end()); // Convert set to vector
                            // std::sort(unionVector.begin(), unionVector.end()); // Sort the vector
                            if (!DP_enable[unionSet]) {
                                auto x = unionSet;
                                std::vector<int> current;
                                for (int i = 0; x > 0; ++i) {
                                    if (x & 1) {
                                        current.push_back(i);
                                    }
                                    x >>= 1;
                                }
                                /*****************************/
                                if (current.size() == 1) {
                                    DP_enable[unionSet] = true;
                                    DP[unionSet] = true;
                                } else {
                                    std::string assertion = "(and";
                                    for (unsigned i=1; i<current.size(); ++i) {
                                        const auto &c1 = ratioMap[current[i-1]];
                                        const auto &c2 = ratioMap[current[i]];
                                        assertion += " (= (- (* " + c1.first.realToSMT() + " " + c2.second.realToSMT() + ") (* " + c1.first.imagToSMT() + " " + c2.second.imagToSMT() + ")) (- (* " + c1.second.realToSMT() + " " + c2.first.realToSMT() + ") (* " + c1.second.imagToSMT() + " " + c2.first.imagToSMT() + ")))";
                                        assertion += " (= (+ (* " + c1.first.realToSMT() + " " + c2.second.imagToSMT() + ") (* " + c1.first.imagToSMT() + " " + c2.second.realToSMT() + ")) (+ (* " + c1.second.realToSMT() + " " + c2.first.imagToSMT() + ") (* " + c1.second.imagToSMT() + " " + c2.first.realToSMT() + ")))";
                                    }
                                    for (unsigned i=0; i<current.size(); i++) {
                                        const auto &c = ratioMap[current[i]];
                                        assertion += " (or"; // assertion += " (or () ())";
                                        assertion += " (and (= " + c.first.realToSMT() + " 0)(= " + c.first.imagToSMT() + " 0)(= " + c.second.realToSMT() + " 0)(= " + c.second.imagToSMT() + " 0))"; // (cq == 0 && cr == 0) || (cq != 0 && cr != 0)
                                        assertion += " (and (or (not (= " + c.first.realToSMT() + " 0))(not (= " + c.first.imagToSMT() + " 0)))(or (not (= " + c.second.realToSMT() + " 0))(not (= " + c.second.imagToSMT() + " 0))))";
                                        assertion += ")";
                                    }
                                    assertion += ")";
                                    DP_enable[unionSet] = true;
                                    DP[unionSet] = call_SMT_solver(constraintR + constraintQ, assertion);
                                }
                            }
                            if (!DP[unionSet]) {
                                continue;
                            }
                            /*********************************************/
                            // Line 16
                            for (const auto &sq : sqSet) {
                                Uq_.insert(std::make_pair(sq, unionSet));
                            }
                            /*********************************************/
                        }
                    }
                    /*********************************************/
                    // Line 17-18
                    for (const auto &sr_ : Hr) {
                        if (!processed[sr_].contains(Uq_) && !worklist[sr_].contains(Uq_)) {
                            #ifdef MIN
                            auto copy = worklist[sr_]; // Min{...}
                            for (const auto &t : copy) {
                                if (std::includes(t.begin(), t.end(), Uq_.begin(), Uq_.end()))
                                    worklist[sr_].erase(t);
                            }
                            bool cancel = false;
                            for (const auto &t : worklist[sr_]) {
                                if (std::includes(Uq_.begin(), Uq_.end(), t.begin(), t.end())) {
                                    cancel = true;
                                    break;
                                }
                            }
                            if (!cancel)
                            #endif
                                worklist[sr_].insert(Uq_);
                            // std::cout << AUTOQ::Util::Convert::ToString(worklist) << "\n";
                        }
                    }
                    /*********************************************/
                }
            }
        }
        auto sr2 = sr;
        const auto &Uq2 = Uq;
        for (const auto &kv : processed) {
            auto sr1 = kv.first;
            for (const auto &Uq1 : kv.second) {
                if (sr1 == sr2 && Uq1 == Uq2) continue;
                for (const auto &tr : R_transitions) {
                    const auto &alpha = tr.first;
                    /*********************************************/
                    // Line 11
                    auto Hr_ptr = tr.second.find({sr1, sr2});
                    if (Hr_ptr == tr.second.end()) continue;
                    StateSet Hr = Hr_ptr->second;
                    if (Hr.empty()) continue;
                    /*********************************************/
                    StateScaleSet Uq_; // Line 12
                    /*********************************************/
                    // Line 13
                    for (const auto &kv1 : Uq1) {
                        const auto &sq1 = kv1.first;
                        const auto &c1_set = kv1.second;
                        assert(c1_set > 0);
                        for (const auto &kv2 : Uq2) {
                            const auto &sq2 = kv2.first;
                            const auto &c2_set = kv2.second;
                            assert(c2_set > 0);
                            /*********************************************/
                            // Line 15
                            StateSet sqSet;
                            auto it = Q_transitions.find(alpha);
                            if (it != Q_transitions.end()) {
                                auto ptr = it->second.find({sq1, sq2});
                                if (ptr == it->second.end()) continue;
                                sqSet = ptr->second;
                            }
                            if (sqSet.empty()) continue;
                            // Line 14
                            unsigned unionSet = c1_set | c2_set;
                            // std::vector<int> unionVector(unionSet.begin(), unionSet.end()); // Convert set to vector
                            // std::sort(unionVector.begin(), unionVector.end()); // Sort the vector
                            if (!DP_enable[unionSet]) {
                                auto x = unionSet;
                                std::vector<int> current;
                                for (int i = 0; x > 0; ++i) {
                                    if (x & 1) {
                                        current.push_back(i);
                                    }
                                    x >>= 1;
                                }
                                /*****************************/
                                if (current.size() == 1) {
                                    DP_enable[unionSet] = true;
                                    DP[unionSet] = true;
                                } else {
                                    std::string assertion = "(and";
                                    for (unsigned i=1; i<current.size(); ++i) {
                                        const auto &c1 = ratioMap[current[i-1]];
                                        const auto &c2 = ratioMap[current[i]];
                                        assertion += " (= (- (* " + c1.first.realToSMT() + " " + c2.second.realToSMT() + ") (* " + c1.first.imagToSMT() + " " + c2.second.imagToSMT() + ")) (- (* " + c1.second.realToSMT() + " " + c2.first.realToSMT() + ") (* " + c1.second.imagToSMT() + " " + c2.first.imagToSMT() + ")))";
                                        assertion += " (= (+ (* " + c1.first.realToSMT() + " " + c2.second.imagToSMT() + ") (* " + c1.first.imagToSMT() + " " + c2.second.realToSMT() + ")) (+ (* " + c1.second.realToSMT() + " " + c2.first.imagToSMT() + ") (* " + c1.second.imagToSMT() + " " + c2.first.realToSMT() + ")))";
                                    }
                                    assertion += ")";
                                    DP_enable[unionSet] = true;
                                    DP[unionSet] = call_SMT_solver(constraintR + constraintQ, assertion);
                                }
                            }
                            if (!DP[unionSet]) {
                                continue;
                            }
                            /*********************************************/
                            // Line 16
                            for (const auto &sq : sqSet) {
                                Uq_.insert(std::make_pair(sq, unionSet));
                            }
                            /*********************************************/
                        }
                    }
                    /*********************************************/
                    // Line 17-18
                    for (const auto &sr_ : Hr) {
                        if (!processed[sr_].contains(Uq_) && !worklist[sr_].contains(Uq_)) {
                            #ifdef MIN
                            auto copy = worklist[sr_]; // Min{...}
                            for (const auto &t : copy) {
                                if (std::includes(t.begin(), t.end(), Uq_.begin(), Uq_.end()))
                                    worklist[sr_].erase(t);
                            }
                            bool cancel = false;
                            for (const auto &t : worklist[sr_]) {
                                if (std::includes(Uq_.begin(), Uq_.end(), t.begin(), t.end())) {
                                    cancel = true;
                                    break;
                                }
                            }
                            if (!cancel)
                            #endif
                                worklist[sr_].insert(Uq_);
                            // std::cout << AUTOQ::Util::Convert::ToString(worklist) << "\n";
                        }
                    }
                    /*********************************************/
                }
            }
        }
    }
    auto duration = chrono::steady_clock::now() - start;
    std::cout << toString2(duration) << "\n";
    return true;
}

template <typename Symbol>
std::vector<std::vector<std::string>> AUTOQ::Automata<Symbol>::print(const std::map<typename AUTOQ::Automata<Symbol>::State, std::set<typename AUTOQ::Automata<Symbol>::Symbol>> &leafSymbolMap, int qubit, typename AUTOQ::Automata<Symbol>::State state) const {
    if (qubit == static_cast<int>(qubitNum + 1)) {
        std::vector<std::vector<std::string>> ans;
        for (const auto &t : leafSymbolMap.at(state)) {
            std::stringstream ss;
            ss << t;
            ans.push_back({ss.str()});
        }
        return ans;
    }
    std::vector<std::vector<std::string>> ans;
    for (const auto &out_ins : transitions.at({qubit})) {
        if (out_ins.first == state) {
            for (const auto &in : out_ins.second) {
                auto v1 = print(leafSymbolMap, qubit + 1, in.at(0));
                auto v2 = print(leafSymbolMap, qubit + 1, in.at(1));
                for (const auto &s1 : v1) {
                    for (const auto &s2 : v2) {
                        auto v = s1;
                        v.insert(v.end(), s2.begin(), s2.end());
                        ans.push_back(v);
                    }
                }
            }
        }
    }
    return ans;
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::print_language(const char *str) const {
    std::cout << str;
    std::map<typename AUTOQ::Automata<Symbol>::State, std::set<typename AUTOQ::Automata<Symbol>::Symbol>> leafSymbolMap;
    for (const auto &t : transitions) { // construct the map from state to leaf symbol
        if (t.first.is_leaf()) {
            for (const auto &out_ins : t.second) {
                // if (out_ins.second.contains({}))
                    leafSymbolMap[out_ins.first].insert(t.first.symbol());
            }
        }
    }
    for (const auto &s : finalStates) {
        auto v = print(leafSymbolMap, 1, s);
        for (const auto &s : v) {
            std::map<std::string, int> count;
            for (unsigned i=0; i<s.size(); i++)
                count[s[i]]++;
            auto ptr = std::max_element(count.begin(), count.end(), [](const auto &x, const auto &y) {
                return x.second < y.second;
            });
            for (unsigned i=0; i<s.size(); i++) {
                if (s[i] != (ptr->first))
                    std::cout << boost::dynamic_bitset(qubitNum, i) << ":" << s[i] << " ";
            }
            std::cout << "*:" << (ptr->first) << std::endl;
        }
    }
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;