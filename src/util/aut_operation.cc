#include <autoq/aut_description.hh>
#include <autoq/complex/complex.hh>
#include <autoq/symbol/concrete.hh>
#include <autoq/symbol/symbolic.hh>
#include <autoq/symbol/predicate.hh>
#include <autoq/util/util.hh>
#include <autoq/inclusion.hh>
#include <autoq/serialization/timbuk_serializer.hh>

#include "simulation/explicit_lts.hh"

#include <fstream>
#include <numeric>
#include <chrono>
#include <queue>
#include <regex>
#include <bit>
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
    TransitionMap transitions_new;
    std::map<State, State> stateOldToNew;
    for (const auto &t : transitions) {
        for (const auto &in_out : t.second) {
            const auto &outs = in_out.second;
            StateVector sv;
            for (const auto &v : in_out.first) { // we construct the new tuple
                State newState = stateOldToNew.size();
                auto itBoolPair = stateOldToNew.insert({v, newState});
                if (!itBoolPair.second) { // if insertion didn't happened
                    const auto& it = itBoolPair.first;
                    newState = it->second;
                }
                sv.push_back(newState);
            }
            for (const auto &s : outs) {
                State newState = stateOldToNew.size();
                auto itBoolPair = stateOldToNew.insert({s, newState});
                if (!itBoolPair.second) { // if insertion didn't happened
                    const auto& it = itBoolPair.first;
                    newState = it->second;
                }
                transitions_new[t.first][sv].insert(newState);
            }
        }
    }
    transitions = transitions_new;
    StateVector finalStates_new; // TODO: Can we set the initial capacity?
    finalStates_new.reserve(finalStates.size());
    for (const auto &s : finalStates) {
        auto it = stateOldToNew.find(s);
        if (it != stateOldToNew.end()) {
            finalStates_new.push_back(it->second);
        }
        // We do not add the untouched final states here, since
        // it could severely degrade the performance (either with or without sim_reduce()).
    }
    finalStates = finalStates_new;
    stateNum = stateOldToNew.size();
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::remove_impossible_colors() {
    std::map<Symbol, std::map<State, std::map<Tag, std::vector<StateVector>>>> fqci;
    for (const auto &tr : transitions) {
        auto &symbol_tag = tr.first;
        auto &in_outs = tr.second;
        for (const auto &in_out : in_outs) {
            auto &in = in_out.first;
            auto &outs = in_out.second;
            for (const auto &out : outs) {
                fqci[symbol_tag.symbol()][out][symbol_tag.tag()].push_back(in);
            }
        }
    }

    std::map<Symbol, std::map<State, std::vector<Tag>>> delete_colors;
    for (const auto &f_ : fqci) {
        for (const auto &q_ : f_.second) {
            for (auto q_ptr = q_.second.rbegin(); q_ptr != q_.second.rend(); ++q_ptr) {
                if (q_ptr->second.size() >= 2) {
                    delete_colors[f_.first][q_.first].push_back(q_ptr->first);
                }
                else {
                    for (auto q_ptr2 = q_.second.begin(); q_ptr2 != q_.second.end(); ++q_ptr2) {
                        if (q_ptr2->first >= q_ptr->first) break;
                        if ((q_ptr->first | q_ptr2->first) == q_ptr->first) {
                            delete_colors[f_.first][q_.first].push_back(q_ptr->first);
                            break;
                        }
                    }
                }
            }
        }
    }

    for (const auto &f_ : delete_colors) {
        for (const auto &q_ : f_.second) {
            for (const auto &c : q_.second) {
                std::vector<StateVector> to_be_deleted;
                for (auto &in_outs : transitions[{f_.first, c}]) {
                    in_outs.second.erase(q_.first);
                    if (in_outs.second.empty())
                        to_be_deleted.push_back(in_outs.first);
                }
                for (const auto &in : to_be_deleted)
                    transitions[{f_.first, c}].erase(in);
            }
        }
    }
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::remove_useless(bool only_bottom_up) {
    auto start = std::chrono::steady_clock::now();
    remove_impossible_colors();

    bool changed;
    std::vector<bool> traversed(stateNum, false);
    TransitionMap transitions_remaining = transitions;
    TransitionMap transitions_mother;

    /*******************
     * Part 1: Bottom-Up
     *******************/
    do {
        changed = false;
        transitions_mother = transitions_remaining;
        for (const auto &t : transitions_mother) {
            const auto &symbol_tag = t.first;
            for (const auto &in_out : t.second) {
                const auto &in = in_out.first;
                const auto &outs = in_out.second;
                bool input_traversed = in.empty();
                if (!input_traversed) {
                    input_traversed = true;
                    for (const auto &s : in)
                        input_traversed &= traversed[s];
                }
                if (input_traversed) {
                    for (const auto &s : outs)
                        traversed[s] = true;
                    transitions_remaining.at(symbol_tag).erase(in);
                    changed = true;
                }
            }
            if (transitions_remaining.at(symbol_tag).empty())
                transitions_remaining.erase(symbol_tag);
        }
    } while(changed);
    for (const auto &t : transitions_remaining) {
        const auto &symbol_tag = t.first;
        for (const auto &in_out : t.second)
            transitions.at(symbol_tag).erase(in_out.first);
        if (transitions.at(symbol_tag).empty())
            transitions.erase(symbol_tag);
    }

    /******************
     * Part 2: Top-Down
     ******************/
    if (!only_bottom_up) {
        traversed = std::vector<bool>(stateNum, false);
        for (const auto &s : finalStates)
            traversed[s] = true;
        transitions_remaining = transitions;
        do {
            changed = false;
            transitions_mother = transitions_remaining;
            for (const auto &t : transitions_mother) {
                const auto &symbol_tag = t.first;
                for (const auto &in_out : t.second) {
                    const auto &in = in_out.first;
                    const auto &outs = in_out.second;
                    for (const auto &s : outs) {
                        if (traversed[s]) {
                            for (const auto &v : in)
                                traversed[v] = true;
                            transitions_remaining.at(symbol_tag).at(in).erase(s);
                            changed = true;
                        }
                    }
                    if (transitions_remaining.at(symbol_tag).at(in).empty())
                        transitions_remaining.at(symbol_tag).erase(in);
                }
                if (transitions_remaining.at(symbol_tag).empty())
                    transitions_remaining.erase(symbol_tag);
            }
        } while(changed);
        for (const auto &t : transitions_remaining) {
            const auto &symbol_tag = t.first;
            for (const auto &in_out : t.second) {
                for (const auto &s : in_out.second)
                    transitions.at(symbol_tag).at(in_out.first).erase(s);
                if (transitions.at(symbol_tag).at(in_out.first).empty())
                    transitions.at(symbol_tag).erase(in_out.first);
            }
            if (transitions.at(symbol_tag).empty())
                transitions.erase(symbol_tag);
        }
    }
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
            // assert(symbol_tag.tag().size() <= 1);
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

// template <typename Symbol>
// void AUTOQ::Automata<Symbol>::branch_restriction(int k, bool positive_has_value) {
//     auto start = std::chrono::steady_clock::now();
//     State num_of_states = stateNum;
//     if (stateNum > std::numeric_limits<State>::max() / 2)
//         throw std::overflow_error("[ERROR] The number of states is too large.");
//     stateNum *= 2;

//     TransitionMap transitions_copy = transitions;
//     for (const auto &t : transitions_copy) {
//         const SymbolTag &symbol_tag = t.first;
//         if (symbol_tag.is_internal()) { // x_i + determinized number
//             auto &in_outs_dest = transitions.at(symbol_tag);
//             for (const auto &in_out : t.second) {
//                 StateVector in;
//                 assert(in_out.first.size() == 2);
//                 for (unsigned i=0; i<in_out.first.size(); i++)
//                     in.push_back(in_out.first[i] + num_of_states);
//                 StateSet out;
//                 for (const auto &n : in_out.second)
//                     out.insert(n + num_of_states);
//                 in_outs_dest.insert(make_pair(in, out)); // duplicate this internal transition
//             }
//         } else { // (a,b,c,d,k)
//             assert(symbol_tag.is_leaf());
//             for (const auto &in_out : t.second) {
//                 assert(in_out.first.empty());
//                 for (const auto &n : in_out.second) { // Note we do not change k.
//                     SymbolTag s = symbol_tag;
//                     s.symbol().back_to_zero();
//                     transitions[s][{}].insert(n + num_of_states); // duplicate this leaf transition
//                 }
//             }
//         }
//     }

//     transitions_copy = transitions;
//     for (const auto &t : transitions_copy) {
//         const SymbolTag &symbol_tag = t.first;
//         if (symbol_tag.is_internal() && symbol_tag.symbol().qubit() == k) { // x_i + determinized number
//             auto &in_outs_dest = transitions.at(symbol_tag);
//             for (const auto &in_out : t.second) {
//                 assert(in_out.first.size() == 2);
//                 StateVector sv = in_out.first;
//                 if (in_out.first[0] < num_of_states && in_out.first[1] < num_of_states) {
//                     if (positive_has_value) {
//                         sv[0] = in_out.first[0] + num_of_states;
//                     } else {
//                         sv[1] = in_out.first[1] + num_of_states;
//                     }
//                     in_outs_dest.erase(in_out.first);
//                     in_outs_dest.insert(make_pair(sv, in_out.second));
//                 }
//             }
//         }
//     }
//     remove_useless(); // otherwise, will out of memory
//     auto end = std::chrono::steady_clock::now();
//     branch_rest_time += end - start;
//     if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
// }

// template <typename Symbol>
// void AUTOQ::Automata<Symbol>::semi_determinize() {
//     if (isTopdownDeterministic) return;
//     TransitionMap transitions_copy = transitions;
//     for (const auto &t : transitions_copy) {
//         const SymbolTag &symbol_tag = t.first;
//         if (symbol_tag.is_internal()) { // x_i not determinized yet
//             assert(!symbol_tag.is_tagged()); // not determinized yet
//             transitions.erase(symbol_tag); // modify
//             int counter = 0;
//             SymbolTag new_symbol;
//             new_symbol.symbol() = symbol_tag.symbol();
//             for (const auto &in_out : t.second) {
//                 new_symbol.tag().push_back(counter++);
//                 std::map<StateVector, StateSet> value;
//                 value.insert(in_out);
//                 transitions.insert(std::make_pair(new_symbol, value)); // modify
//                 new_symbol.tag().pop_back();
//             }
//         }
//     }
//     // DO NOT reduce here.
//     if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
// }

// template <typename Symbol>
// void AUTOQ::Automata<Symbol>::semi_undeterminize() {
//     if (isTopdownDeterministic) return;
//     TransitionMap transitions_copy = transitions;
//     for (const auto &t : transitions_copy) {
//         const SymbolTag &symbol_tag = t.first;
//         if (symbol_tag.is_internal()) { // pick all determinized x_i's
//             assert(symbol_tag.is_tagged()); // determinized
//             transitions.erase(symbol_tag); // modify
//             for (const auto &in_out : t.second) {
//                 for (const auto &v : in_out.second)
//                     transitions[symbol_tag.symbol()][in_out.first].insert(v); // modify
//             }
//         }
//     }
//     this->reduce();
//     if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
// }

// #define construct_product_state_id(a, b, i) \
//     State i; \
//     if (overflow) { \
//         auto it = stateOldToNew.find(std::make_pair(a, b)); \
//         if (it == stateOldToNew.end()) { \
//             i = stateOldToNew.size(); \
//             stateOldToNew[std::make_pair(a, b)] = i; \
//         } \
//         else i = it->second; \
//     } else i = a * o.stateNum + b;
// template <typename Symbol>
// AUTOQ::Automata<Symbol> AUTOQ::Automata<Symbol>::binary_operation(const Automata<Symbol> &o, bool add) {
//     auto start = std::chrono::steady_clock::now();
//     AUTOQ::Automata<Symbol> result;
//     result.name = name;
//     result.qubitNum = qubitNum;
//     result.isTopdownDeterministic = isTopdownDeterministic; // IMPORTANT: Avoid missing copying new fields afterwards.

//     std::map<std::pair<State, State>, State> stateOldToNew; // used only if overflow := true;
//     bool overflow = (stateNum > std::numeric_limits<State>::max() / o.stateNum);
//     if (!overflow)
//         result.finalStates.reserve(finalStates.size() * o.finalStates.size()); // TODO: Can we set the initial capacity?
//     else
//         throw std::overflow_error("[ERROR] The number of states after multiplication is too large.");

//     for (const auto &fs1 : finalStates)
//         for (const auto &fs2 : o.finalStates) {
//             construct_product_state_id(fs1, fs2, i);
//             result.finalStates.push_back(i);
//         }

//     // We assume here transitions are ordered by symbols.
//     // x_i are placed in the beginning, and leaves are placed in the end.
//     // This traversal method is due to efficiency.
//     std::vector<bool> previous_level_states2(stateNum * o.stateNum);
//     std::vector<bool> previous_level_states(stateNum * o.stateNum);
//     for (auto s : result.finalStates)
//         previous_level_states[s] = true;
//     std::vector<bool> next_level_states;
//     auto it = transitions.begin();
//     auto it2 = o.transitions.begin();
//     for (; it != transitions.end(); it++) { // iterate over all internal transitions of T1
//         if (it->first.is_leaf()) break; // internal
//         if (it->first < it2->first) continue;
//         while (it2 != o.transitions.end() && it->first > it2->first)
//             it2++;
//         if (it2 == o.transitions.end()) break;
//         if (it->first < it2->first) continue;
//         assert(it->first == it2->first); // Ensure T1's and T2's current transitions have the same symbol now.
//         // Update previous_level_states.
//         if (it != transitions.begin() && it->first.symbol().qubit() != std::prev(it)->first.symbol().qubit()) { // T1 changes level.
//             previous_level_states = previous_level_states2;
//             previous_level_states2 = std::vector<bool>(stateNum * o.stateNum);
//         }
//         // Update next_level_states.
//         if (it == transitions.begin() || it->first.symbol().qubit() != std::prev(it)->first.symbol().qubit()) { // T1 goes into the new level.
//             next_level_states = std::vector<bool>(stateNum * o.stateNum);
//             auto it3 = it; // it3 indicates the next level of it.
//             while (it3 != transitions.end() && it3->first.is_internal() && it3->first.symbol().qubit() == it->first.symbol().qubit())
//                 it3++;
//             if (it3 == transitions.end()) {} // T1 has no leaf transitions?
//             else if (it3->first.is_leaf()) { // The next level of T1 is leaf transitions.
//                 auto it4 = it2; // Initially it2 has the same symbol as it.
//                 while (it4 != o.transitions.end() && it4->first.is_internal())
//                     it4++;
//                 auto it4i = it4;
//                 // We hope it4 currently points to the first leaf transition.
//                 // If it4 points to o.transitions.end(), then the following loop will not be executed.
//                 for (; it3 != transitions.end(); it3++) { // iterate over all leaf transitions of T1
//                     assert(it3->first.is_leaf());
//                     for (it4 = it4i; it4 != o.transitions.end(); it4++) { // iterate over all leaf transitions of T2
//                         assert(it4->first.is_leaf());
//                         for (const auto &s1 : it3->second.begin()->second) { // iterate over all output states of it3
//                             for (const auto &s2 : it4->second.begin()->second) { // iterate over all output states of it4
//                                 construct_product_state_id(s1, s2, i);
//                                 next_level_states[i] = true; // collect all output state products of the next level
//                             }
//                         }
//                     }
//                 }
//             } else { // The next level of T1 is still internal transitions.
//                 int current_level = static_cast<int>(it3->first.symbol().qubit());
//                 auto it4 = it2; // Initially it2 has the same symbol as it.
//                 while (it4 != o.transitions.end() && it4->first.is_internal() && it4->first.symbol().qubit() == current_level)
//                     it4++;
//                 // We hope it4 currently points to T2's first transition of the next level.
//                 // If it4 points to o.transitions.end(), then the following loop will not be executed.
//                 for (; it3->first.is_internal() && it3->first.symbol().qubit() == current_level; it3++) {
//                     if (it3->first < it4->first) continue;
//                     while (it4 != o.transitions.end() && it3->first > it4->first)
//                         it4++;
//                     if (it4 == o.transitions.end()) break;
//                     if (it3->first < it4->first) continue;
//                     assert(it3->first == it4->first);
//                     // Ensure T1's and T2's current transitions have the same symbol now.
//                     for (auto itt = it3->second.begin(); itt != it3->second.end(); itt++) { // all input-output pairs of it3
//                         for (auto itt2 = it4->second.begin(); itt2 != it4->second.end(); itt2++) { // all input-output pairs of it4
//                             for (const auto &s1 : itt->second) { // all output states of it3
//                                 for (const auto &s2 : itt2->second) { // all output states of it4
//                                     construct_product_state_id(s1, s2, i);
//                                     next_level_states[i] = true; // collect all output state products of the next level
//                                 }
//                             }
//                         }
//                     }
//                 }
//             }
//         }
//         std::map<StateVector, StateSet> m;
//         for (auto itt = it->second.begin(); itt != it->second.end(); itt++) { // iterate over all input-output pairs of it
//             for (auto itt2 = it2->second.begin(); itt2 != it2->second.end(); itt2++) { // iterate over all input-output pairs of it2
//                 StateVector sv;
//                 StateSet ss;
//                 construct_product_state_id(itt->first[0], itt2->first[0], i);
//                 if (!next_level_states[i]) continue;
//                 sv.push_back(i); // construct product of T1's and T2's left input states
//                 construct_product_state_id(itt->first[1], itt2->first[1], j);
//                 if (!next_level_states[j]) continue;
//                 sv.push_back(j); // construct product of T1's and T2's right input states
//                 for (const auto &s1 : itt->second) { // all output states of itt
//                     for (const auto &s2 : itt2->second) { // all output states of itt2
//                         construct_product_state_id(s1, s2, i);
//                         if (previous_level_states[i])
//                             ss.insert(i);
//                     }
//                 }
//                 if (ss.size() > 0) {
//                     previous_level_states2[sv[0]] = true;
//                     previous_level_states2[sv[1]] = true;
//                     m.insert(std::make_pair(sv, ss));
//                 }
//             }
//         }
//         result.transitions.insert(make_pair(it->first, m));
//         assert(m.begin()->first.size() == 2);
//     }
//     previous_level_states = previous_level_states2;
//     // We now advance it2 to T2's first leaf transition.
//     while (it2 != o.transitions.end() && !it2->first.is_leaf())
//         it2++;
//     for (; it != transitions.end(); it++) {
//         assert(it->first.is_leaf());
//         for (auto it2t = it2; it2t != o.transitions.end(); it2t++) { // it2 as the new begin point.
//             assert(it2t->first.is_leaf());
//             Symbol symbol;
//             if (add) symbol = it->first.symbol() + it2t->first.symbol();
//             else symbol = it->first.symbol() - it2t->first.symbol();
//             for (const auto &s1 : it->second.begin()->second)
//                 for (const auto &s2 : it2t->second.begin()->second) {
//                     construct_product_state_id(s1, s2, i);
//                     if (previous_level_states[i]) {
//                         assert(it->first.tag() == it2t->first.tag()); // untagged
//                         result.transitions[{symbol, it->first.tag()}][{}].insert(i);
//                     }
//                 }
//         }
//     }
//     if (overflow)
//         result.stateNum = stateOldToNew.size();
//     else
//         result.stateNum = stateNum * o.stateNum;
//     result.remove_useless(true); // otherwise, will out of memory
//     // Round several approximately equal floating points to the same value!
//     #if COMPLEX != 1
//         result.fraction_simplification();
//     #endif
//     auto end = std::chrono::steady_clock::now();
//     binop_time += end - start;
//     if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
//     return result;
// }
// template <typename Symbol>
// AUTOQ::Automata<Symbol> Automata<Symbol>::operator+(const Automata &o) {
//     return binary_operation(o, true);
// }
// template <typename Symbol>
// AUTOQ::Automata<Symbol> Automata<Symbol>::operator-(const Automata &o) {
//     return binary_operation(o, false);
// }

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::uniform(int n) {
    TreeAutomata aut;
    aut.name = "Uniform";
    aut.qubitNum = n;
    for (int level=1; level<=n; level++) {
        aut.transitions[{level}][{level, level}].insert(level-1);
    }
    aut.transitions[Concrete(Complex::Complex::One().divide_by_the_square_root_of_two(n))][{}].insert(n);
    aut.finalStates.push_back(0);
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
            aut.transitions[{level}][{2*level - 1, 2*level - 1}] = {2*level - 3};
        aut.transitions[{level, 0b01}][{2*level - 1, 2*level}] = {2*level - 2};
        aut.transitions[{level, 0b10}][{2*level, 2*level - 1}] = {2*level - 2};
    }
    aut.transitions[Concrete(Complex::Complex::One())][{}] = {2*n};
    aut.transitions[Concrete(Complex::Complex::Zero())][{}] = {2*n - 1};
    aut.finalStates.push_back(0);
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
            aut.transitions[{level}][{state_counter*2+1, state_counter*2+2}] = {state_counter};
            state_counter++;
        }
        pow_of_two *= 2;
    }
    for (State i=state_counter; i<=state_counter*2; i++) {
        aut.transitions[Concrete(Complex::Complex::Rand())][{}].insert(i);
    }
    aut.finalStates.push_back(0);
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
    aut.finalStates.push_back(0);
    aut.transitions[{1}][{2,1}] = {0};
    for (int level=2; level<=n; level++) {
        aut.transitions[{level}][{level*2-1, level*2-1}] = {level*2-3};
        aut.transitions[{level}][{level*2, level*2-1}] = {level*2-2};
    }
    aut.transitions[Concrete(Complex::Complex::Zero())][{}].insert(n*2-1);
    aut.transitions[Concrete(Complex::Complex::One())][{}].insert(n*2);
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
            aut.transitions[{level}][{2*level - 1, 2*level - 1}] = {2*level - 3};
        aut.transitions[{level, 0b01}][{2*level - 1, 2*level}] = {2*level - 2};
        aut.transitions[{level, 0b10}][{2*level, 2*level - 1}] = {2*level - 2};
    }
    for (int level=1; level<=n; level++) {
        aut.transitions[{n + level}][{2*n + 2*level-1, 2*n + 2*level-1}] = {2*n + 2*level-3};
        aut.transitions[{n + level}][{2*n + 2*level, 2*n + 2*level-1}] = {2*n + 2*level-2};
    }
    aut.transitions[{n + (n+1)}][{2*n + 2*(n+1)-1, 2*n + 2*(n+1)-1}] = {2*n + 2*(n+1)-3};
    aut.transitions[{n + (n+1)}][{2*n + 2*(n+1)-1, 2*n + 2*(n+1)}] = {2*n + 2*(n+1)-2};
    if (n >= 3) {
        for (int level=n+2; level<=2*n; level++) {
            aut.transitions[{n + level}][{2*n + 2*level-1, 2*n + 2*level-1}] = {2*n + 2*level-3};
            aut.transitions[{n + level}][{2*n + 2*level, 2*n + 2*level-1}] = {2*n + 2*level-2};
        }
        aut.transitions[Concrete(Complex::Complex::One())][{}] = {6*n};
        aut.transitions[Concrete(Complex::Complex::Zero())][{}] = {6*n - 1};
        aut.stateNum = 6*n + 1;
    } else {
        assert(n == 2);
        aut.transitions[Concrete(Complex::Complex::One())][{}] = {4*n + 2};
        aut.transitions[Concrete(Complex::Complex::Zero())][{}] = {4*n + 1};
        aut.stateNum = 4*n + 3;
    }
	aut.finalStates.push_back(0);
    return aut;
}

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::zero_zero_one_zero(int n) {
    TreeAutomata aut;
    assert(n >= 2);
    aut.name = "Zero_Zero_One_Zero";
    aut.qubitNum = n + (n+1) + (n>=3) * (n-1);

    aut.transitions[{1}][{2,1}] = {0};
    for (int level=2; level<=n; level++) {
        aut.transitions[{level}][{level*2-1, level*2-1}] = {level*2-3};
        aut.transitions[{level}][{level*2, level*2-1}] = {level*2-2};
    }
    for (int level=1; level<=n; level++) {
        aut.transitions[{n + level}][{2*n + 2*level-1, 2*n + 2*level-1}] = {2*n + 2*level-3};
        aut.transitions[{n + level}][{2*n + 2*level, 2*n + 2*level-1}] = {2*n + 2*level-2};
    }
    aut.transitions[{n + (n+1)}][{2*n + 2*(n+1)-1, 2*n + 2*(n+1)-1}] = {2*n + 2*(n+1)-3};
    aut.transitions[{n + (n+1)}][{2*n + 2*(n+1)-1, 2*n + 2*(n+1)}] = {2*n + 2*(n+1)-2};
    if (n >= 3) {
        for (int level=n+2; level<=2*n; level++) {
            aut.transitions[{n + level}][{2*n + 2*level-1, 2*n + 2*level-1}] = {2*n + 2*level-3};
            aut.transitions[{n + level}][{2*n + 2*level, 2*n + 2*level-1}] = {2*n + 2*level-2};
        }
        aut.transitions[Concrete(Complex::Complex::One())][{}] = {6*n};
        aut.transitions[Concrete(Complex::Complex::Zero())][{}] = {6*n - 1};
        aut.stateNum = 6*n + 1;
    } else {
        assert(n == 2);
        aut.transitions[Concrete(Complex::Complex::One())][{}] = {4*n + 2};
        aut.transitions[Concrete(Complex::Complex::Zero())][{}] = {4*n + 1};
        aut.stateNum = 4*n + 3;
    }
	aut.finalStates.push_back(0);
    // aut.isTopdownDeterministic = true;
    return aut;
}

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::zero_one_zero(int n) {
    TreeAutomata aut;
    assert(n >= 2);
    aut.name = "Zero_One_Zero";
    aut.qubitNum = (n+1) + (n>=3) * (n-1);

    aut.transitions[{1}][{2,1}] = {0};
    for (int level=2; level<=n; level++) {
        aut.transitions[{level}][{level*2-1, level*2-1}] = {level*2-3};
        aut.transitions[{level}][{level*2, level*2-1}] = {level*2-2};
    }
    aut.transitions[{n+1}][{2*(n+1)-1, 2*(n+1)-1}] = {2*n-1};
    aut.transitions[{n+1}][{2*(n+1)-1, 2*(n+1)}] = {2*n};
    if (n >= 3) {
        for (int level=n+2; level<=2*n; level++) {
            aut.transitions[{level}][{2*level-1, 2*level-1}] = {2*(level-1)-1};
            aut.transitions[{level}][{2*level, 2*level-1}] = {2*(level-1)};
        }
        aut.transitions[Concrete(Complex::Complex::One())][{}] = {4*n};
        aut.transitions[Concrete(Complex::Complex::Zero())][{}] = {4*n - 1};
        aut.stateNum = 4*n + 1;
    } else {
        assert(n == 2);
        aut.transitions[Concrete(Complex::Complex::One())][{}] = {2*n + 2};
        aut.transitions[Concrete(Complex::Complex::Zero())][{}] = {2*n + 1};
        aut.stateNum = 2*n + 3;
    }
	aut.finalStates.push_back(0);
    // aut.isTopdownDeterministic = true;
    return aut;
}

// template <typename Symbol>
// void AUTOQ::Automata<Symbol>::swap_forward(const int k) {
//     if (isTopdownDeterministic) return;
//     for (unsigned next_k=k+1; next_k<=qubitNum; next_k++) {
//         std::map<State, std::vector<std::pair<SymbolTag, StateVector>>> svsv;
//         for (const auto &t : transitions) {
//             const auto &symbol_tag = t.first;
//             const auto &in_outs = t.second;
//             if (symbol_tag.is_internal() && symbol_tag.symbol().qubit() == next_k) {
//                 assert(symbol_tag.tag().size() <= 1);
//                 for (const auto &in_out : in_outs) {
//                     for (const auto &s : in_out.second)
//                         svsv[s].push_back(make_pair(symbol_tag, in_out.first));
//                 }
//             }
//         }
//         std::vector<SymbolTag> to_be_removed2;
//         TransitionMap to_be_removed, to_be_inserted;
//         for (const auto &t : transitions) {
//             const SymbolTag &symbol_tag = t.first;
//             if (symbol_tag.is_internal() && symbol_tag.symbol().qubit() == k) {
//                 for (const auto &in_out : t.second) {
//                     assert(in_out.first.size() == 2);
//                     for (const auto &ssv1 : svsv[in_out.first[0]]) {
//                         for (const auto &ssv2 : svsv[in_out.first[1]]) {
//                             to_be_removed[ssv1.first][ssv1.second].insert(in_out.first[0]);
//                             to_be_removed[ssv2.first][ssv2.second].insert(in_out.first[1]);
//                             if (to_be_inserted[symbol_tag][{ssv1.second[0], ssv2.second[0]}].empty()) {
//                                 if (transitions[symbol_tag][{ssv1.second[0], ssv2.second[0]}].empty())
//                                     to_be_inserted[symbol_tag][{ssv1.second[0], ssv2.second[0]}].insert(stateNum++);
//                                 else
//                                     to_be_inserted[symbol_tag][{ssv1.second[0], ssv2.second[0]}].insert(*(transitions[symbol_tag][{ssv1.second[0], ssv2.second[0]}].begin()));
//                             }
//                             if (to_be_inserted[symbol_tag][{ssv1.second[1], ssv2.second[1]}].empty()) {
//                                 if (transitions[symbol_tag][{ssv1.second[1], ssv2.second[1]}].empty())
//                                     to_be_inserted[symbol_tag][{ssv1.second[1], ssv2.second[1]}].insert(stateNum++);
//                                 else
//                                     to_be_inserted[symbol_tag][{ssv1.second[1], ssv2.second[1]}].insert(*(transitions[symbol_tag][{ssv1.second[1], ssv2.second[1]}].begin()));
//                             }
//                             for (const auto &s : in_out.second)
//                                 to_be_inserted[{Symbol(next_k), {ssv1.first.tag(0), ssv2.first.tag(0)}}][{*(to_be_inserted[symbol_tag][{ssv1.second[0], ssv2.second[0]}].begin()), *(to_be_inserted[symbol_tag][{ssv1.second[1], ssv2.second[1]}].begin())}].insert(s);
//                         }
//                     }
//                 }
//                 to_be_removed2.push_back(symbol_tag);
//             }
//         }
//         for (const auto &v : to_be_removed2)
//             transitions.erase(v);
//         for (const auto &t : to_be_removed) {
//             const SymbolTag &symbol_tag = t.first;
//             for (const auto &in_out : t.second) {
//                 for (const auto &s : in_out.second)
//                     transitions[symbol_tag][in_out.first].erase(s);
//                 if (transitions[symbol_tag][in_out.first].empty())
//                     transitions[symbol_tag].erase(in_out.first);
//                 if (transitions[symbol_tag].empty())
//                     transitions.erase(symbol_tag);
//             }
//         }
//         for (const auto &t : to_be_inserted) {
//             const SymbolTag &symbol_tag = t.first;
//             for (const auto &in_out : t.second) {
//                 for (const auto &s : in_out.second) {
//                     transitions[symbol_tag][in_out.first].insert(s);
//                 }
//             }
//         }
//         // DO NOT reduce here.
//     }
//     if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
// }

// template <typename Symbol>
// void AUTOQ::Automata<Symbol>::swap_backward(const int k) {
//     if (isTopdownDeterministic) return;
//     for (int next_k=qubitNum; next_k>k; next_k--) {
//       std::map<State, std::vector<std::pair<SymbolTag, StateVector>>> svsv;
//         for (const auto &t : transitions) {
//             const auto &symbol_tag = t.first;
//             const auto &in_outs = t.second;
//             if (symbol_tag.is_internal() && symbol_tag.symbol().qubit() == k) {
//                 assert(symbol_tag.tag().size() == 1);
//                 for (const auto &in_out : in_outs) {
//                     for (const auto &s : in_out.second)
//                         svsv[s].push_back(make_pair(symbol_tag, in_out.first));
//                 }
//             }
//         }
//         std::vector<SymbolTag> to_be_removed2;
//         TransitionMap to_be_removed, to_be_inserted;
//         for (const auto &t : transitions) {
//             const SymbolTag &symbol_tag = t.first;
//             if (symbol_tag.is_internal() && symbol_tag.symbol().qubit() == next_k) {
//                 assert(symbol_tag.tag().size() == 2);
//                 for (const auto &in_out : t.second) {
//                     assert(in_out.first.size() == 2);
//                     for (const auto &ssv1 : svsv[in_out.first[0]]) {
//                         for (const auto &ssv2 : svsv[in_out.first[1]]) {
//                             if (ssv1.first == ssv2.first) {
//                                 to_be_removed[ssv1.first][ssv1.second].insert(in_out.first[0]);
//                                 to_be_removed[ssv2.first][ssv2.second].insert(in_out.first[1]);
//                                 SymbolTag t1 = {symbol_tag.symbol(), {symbol_tag.tag(0)}};
//                                 if (to_be_inserted[t1][{ssv1.second[0], ssv2.second[0]}].empty()) {
//                                     if (transitions[t1][{ssv1.second[0], ssv2.second[0]}].empty())
//                                         to_be_inserted[t1][{ssv1.second[0], ssv2.second[0]}].insert(stateNum++);
//                                     else
//                                         to_be_inserted[t1][{ssv1.second[0], ssv2.second[0]}].insert(*(transitions[t1][{ssv1.second[0], ssv2.second[0]}].begin()));
//                                 }
//                                 SymbolTag t2 = {symbol_tag.symbol(), {symbol_tag.tag(1)}};
//                                 if (to_be_inserted[t2][{ssv1.second[1], ssv2.second[1]}].empty()) {
//                                     if (transitions[t2][{ssv1.second[1], ssv2.second[1]}].empty())
//                                         to_be_inserted[t2][{ssv1.second[1], ssv2.second[1]}].insert(stateNum++);
//                                     else
//                                         to_be_inserted[t2][{ssv1.second[1], ssv2.second[1]}].insert(*(transitions[t2][{ssv1.second[1], ssv2.second[1]}].begin()));
//                                 }
//                                 assert(k == ssv1.first.symbol().qubit());
//                                 for (const auto &s : in_out.second)
//                                     to_be_inserted[ssv1.first][{*(to_be_inserted[t1][{ssv1.second[0], ssv2.second[0]}].begin()), *(to_be_inserted[t2][{ssv1.second[1], ssv2.second[1]}].begin())}].insert(s);
//                             }
//                         }
//                     }
//                 }
//                 to_be_removed2.push_back(symbol_tag);
//             }
//         }
//         for (const auto &v : to_be_removed2)
//             transitions.erase(v);
//         for (const auto &t : to_be_removed) {
//             const SymbolTag &symbol_tag = t.first;
//             for (const auto &in_out : t.second) {
//                 for (const auto &s : in_out.second)
//                     transitions[symbol_tag][in_out.first].erase(s);
//                 if (transitions[symbol_tag][in_out.first].empty())
//                     transitions[symbol_tag].erase(in_out.first);
//                 if (transitions[symbol_tag].empty())
//                     transitions.erase(symbol_tag);
//             }
//         }
//         for (const auto &t : to_be_inserted) {
//             const SymbolTag &symbol_tag = t.first;
//             for (const auto &in_out : t.second) {
//                 for (const auto &s : in_out.second) {
//                     transitions[symbol_tag][in_out.first].insert(s);
//                 }
//             }
//         }
//         // DO NOT reduce here.
//     }
//     if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
// }

// template <typename Symbol>
// void AUTOQ::Automata<Symbol>::value_restriction(int k, bool branch) {
//     auto start = std::chrono::steady_clock::now();
//     swap_forward(k);
//     TransitionMap to_be_inserted;
//     std::vector<SymbolTag> to_be_removed;
//     for (const auto &t : transitions) {
//         const SymbolTag &symbol_tag = t.first;
//         if (symbol_tag.is_internal() && symbol_tag.symbol().qubit() == k) {
//             to_be_removed.push_back(symbol_tag);
//             for (const auto &in_out : t.second) {
//                 assert(in_out.first.size() == 2);
//                 for (const auto &s : in_out.second) {
//                     if (branch)
//                         to_be_inserted[symbol_tag][{in_out.first[1], in_out.first[1]}].insert(s);
//                     else
//                         to_be_inserted[symbol_tag][{in_out.first[0], in_out.first[0]}].insert(s);
//                 }
//             }
//         }
//     }
//     for (const auto &t : to_be_removed) {
//         transitions.erase(t);
//     }
//     for (const auto &t : to_be_inserted) {
//         transitions[t.first] = t.second;
//     }
//     swap_backward(k);
//     this->reduce();
//     auto end = std::chrono::steady_clock::now();
//     value_rest_time += end - start;
//     if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
// }

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
                for (const auto &in_out : t.second) {
                    for (const auto &s : in_out.second) {
                        to_be_inserted[symbol_tag][in_out.first].insert(s);
                    }
                }
            }
        }
    }
    for (const auto &t : to_be_removed) transitions.erase(t);
    for (const auto &t : to_be_inserted) {
        for (const auto &kv : t.second)
            for (const auto &s : kv.second)
                transitions[t.first][kv.first].insert(s);
    }
    // remove_useless();
    // reduce();
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

/**************** Equivalence Checking ****************/
// namespace
// { // anonymous namespace
    // std::string gpath_to_VATA = "";

    // /** returns the path to AUTOQ executable */
    // const std::string& get_vata_path()
    // {
    // // is it cached?
    // if (!gpath_to_VATA.empty()) return gpath_to_VATA;

    // // not cached, get it from ENV
    // const char* path = std::getenv("VATA_PATH");
    // if (nullptr == path) {
    //     throw std::runtime_error("[ERROR] The environment variable VATA_PATH is not found!");
    // }

    // gpath_to_VATA = path;
    // return gpath_to_VATA;
    // }

    // const int MAX_ARG_STRLEN = 131070; // in fact is 131072 on the Internet

  /** checks inclusion of two TAs */
    // template <typename Symbol>
    // bool AUTOQ::Automata<Symbol>::check_inclusion(const std::string& lhsPath, const std::string& rhsPath)
    // {
    // std::string aux;
    // AUTOQ::Util::ShellCmd(get_vata_path() + " incl " + lhsPath + " " + rhsPath, aux);
    // return (aux == "1\n");
    // }

    // template <typename Symbol>
    // bool AUTOQ::Automata<Symbol>::check_inclusion(const Automata<Symbol>& lhsPath, const std::string& rhsPath)
    // {
    // std::string aux;
    // std::string aut1 = TimbukSerializer::Serialize(lhsPath);
    // assert(aut1.length() <= MAX_ARG_STRLEN);
    // AUTOQ::Util::ShellCmd(get_vata_path() + " incl2 '" + aut1 + "' " + rhsPath, aux);
    // return (aux == "1\n");
    // }

    // template <typename Symbol>
    // bool AUTOQ::Automata<Symbol>::check_inclusion(const std::string& lhsPath, const Automata<Symbol>& rhsPath)
    // {
    // std::string aux;
    // std::string aut2 = TimbukSerializer::Serialize(rhsPath);
    // assert(aut2.length() <= MAX_ARG_STRLEN);
    // AUTOQ::Util::ShellCmd(get_vata_path() + " incl3 " + lhsPath + " '" + aut2 + "'", aux);
    // return (aux == "1\n");
    // }

    template <>
    bool AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::check_inclusion(const Automata<AUTOQ::Symbol::Symbolic>& autA, const Automata<AUTOQ::Symbol::Symbolic>& autB)
    {
        exit(1);
    }
    template <typename Symbol>
    bool AUTOQ::Automata<Symbol>::check_inclusion(const Automata<Symbol>& autA, const Automata<Symbol>& autB) {
        auto start_include = std::chrono::steady_clock::now();

        // Part 1: Transform transitions into the new data structure.
        std::vector<std::map<SymbolTag, StateVector>> transA(autA.stateNum);
        std::vector<std::map<Symbol, std::map<Tag, StateVector>>> transB(autB.stateNum);
        for (const auto &t : autA.transitions) {
            const SymbolTag &symbol_tag = t.first;
            const auto &in_outs = t.second;
            for (const auto &in_out : in_outs) {
                for (const auto &s : in_out.second) {
                    transA[s][symbol_tag] = in_out.first;
                    // already assume one (q,fc) corresponds to only one input vector.
                }
            }
        }
        for (const auto &t : autB.transitions) {
            const auto &in_outs = t.second;
            for (const auto &in_out : in_outs) {
                for (const auto &s : in_out.second) {
                    transB[s][t.first.symbol()][t.first.tag()] = in_out.first;
                    // already assume one (q,fc) corresponds to only one input vector.
                }
            }
        }
        typedef std::map<State, StateSet> Cell;
        typedef std::set<Cell> Vertex;
        std::set<Vertex> visited; // Remember visited configurations.
        std::queue<Vertex> bfs; // the queue used for traversing the graph
        Vertex vertex; // current vertex data structure
        // Construct source vertices.
        for (const auto &qA : autA.finalStates) {
            vertex = Vertex();
            for (const auto &qB : autB.finalStates) {
                vertex.insert(Cell({{qA, {qB}}}));
            }
            assert(!visited.contains(vertex));
            visited.insert(vertex);
            bfs.push(vertex);
        }
        // Start the BFS!
        while (!bfs.empty()) {
            vertex = bfs.front();
            // std::cout << AUTOQ::Util::Convert::ToString(vertex) << "\n";
            bfs.pop();
            // List all possible transition combinations of A in this vertex first!
            std::map<State, typename std::map<SymbolTag, StateVector>::iterator> A_transition_combinations;
            std::map<State, Tag> possible_colors_for_qA;
            for (const auto& qA_qBs : *(vertex.begin())) {
                auto qA = qA_qBs.first;
                A_transition_combinations[qA] = transA[qA].begin();
                for (const auto &fc_in : transA[qA]) {
                    possible_colors_for_qA[qA] |= fc_in.first.tag();
                }
            }
            bool have_listed_all_combinationsA = false;
            do { // Construct one new vertex for each possible combination of A's transitions.
                // Print the current combination
                // for (const auto &kv : A_transition_combinations) {
                //     std::cout << kv.first << " " << kv.second.second << " ";
                // }
                // std::cout << std::endl;
                /************************************************************/
                // Check if the current combination is color-consistent.
                // If not, skip this one and continue to the next combination.
                unsigned all_used_colors = 0;
                bool color_consistent = true;
                // Check if there is no any children state derived from the current combination.
                // If it is true, then we shall not create new vertices derived from this one,
                // and we shall judge whether the inclusion does not hold right now.
                bool is_leaf_vertex = true;
                for (const auto &kv : A_transition_combinations) {
                    all_used_colors |= kv.second->first.tag();
                    if (kv.second->second.size() > 0)
                        is_leaf_vertex = false;
                }
                for (const auto &qA_c : possible_colors_for_qA) {
                    if (std::popcount(qA_c.second & all_used_colors) > 1) {
                        color_consistent = false;
                        break;
                    }
                }
                /*************************************************************************/
                // Only pick this combination of A's transitions if it is color-consistent.
                if (color_consistent) {
                    Vertex vertex2;
                    bool vertex_fail = true; // is_leaf_vertex
                    for (const auto &cell : vertex) {
                        Cell cell2;
                        bool cell_fail = false; // is_leaf_vertex
                        bool have_listed_all_combinationsB = false;
                        std::map<State, Tag> possible_colors_for_qB;
                        std::map<State, std::map<Symbol, std::map<Tag, StateVector>::iterator>> B_transition_combinations;
                        for (const auto &kv : A_transition_combinations) {
                            const auto &qA = kv.first;
                            const auto &fc_in = *(kv.second); // the currently picked transition for qA
                            const auto &desired_symbol = fc_in.first.symbol(); // the corresponding symbol
                            const auto &inA = fc_in.second; // the current input vector for qA
                            for (const auto &s : inA) {
                                cell2[s]; // Leave room for B's states for each A's child state.
                            }
                            if (cell.at(qA).empty()) {
                                cell_fail = true; // is_leaf_vertex
                                break;
                            }
                            for (const auto &qB : cell.at(qA)) {
                                /****** Build all possible colors for qB *******/
                                for (const auto &f_cin : transB[qB]) {
                                    for (const auto &c_in : f_cin.second) {
                                        possible_colors_for_qB[qB] |= c_in.first;
                                    }
                                }
                                /***********************************************/
                                if (transB[qB].find(desired_symbol) == transB[qB].end()) {
                                    // If qB has no transitions with the desired symbol,
                                    // simply construct the unique cell without B's states!
                                    have_listed_all_combinationsB = true;
                                } else if (!B_transition_combinations[qB].empty() && B_transition_combinations[qB].begin()->first != desired_symbol) {
                                    // If qB is enforced to take two different symbols together,
                                    // simply construct the unique cell without B's states!
                                    have_listed_all_combinationsB = true;
                                } else {
                                    B_transition_combinations[qB][desired_symbol] = transB[qB][desired_symbol].begin();
                                }
                            }
                        }
                        // No possible combination exists!
                        if (have_listed_all_combinationsB) {
                            cell_fail = true; // is_leaf_vertex
                            vertex2.insert(cell2);
                        }
                        while (!have_listed_all_combinationsB) { // Construct one new cell for each possible combination of B's transitions.
                            // Initialize the current cell.
                            for (auto &kv : cell2) {
                                kv.second.clear();
                            }
                            // Print the current combination
                            // for (const auto &kv : B_transition_combinations) {
                            //     std::cout << kv.first << " " << kv.second.begin()->second.second << " ";
                            // }
                            // std::cout << std::endl;
                            /*************************************************************/
                            // Check if the current combination is color-consistent.
                            // If not, simply construct the unique cell without B's states!
                            bool color_consistent2 = true;
                            unsigned all_used_colors = 0;
                            for (const auto &kv : B_transition_combinations) {
                                all_used_colors |= kv.second.begin()->second->first;
                            }
                            for (const auto &qB_c : possible_colors_for_qB) {
                                if (std::popcount(qB_c.second & all_used_colors) > 1) {
                                    color_consistent2 = false;
                                    break;
                                }
                            }
                            /*************************************************************/
                            if (color_consistent2) {
                                for (const auto &kv : A_transition_combinations) {
                                    const auto &qA = kv.first;
                                    const auto &inA = kv.second->second; // the current input vector for qA
                                    for (const auto &qB : cell.at(qA)) {
                                        const auto &inB = B_transition_combinations[qB].begin()->second->second; // the current input vector for qB
                                        assert(inA.size() == inB.size()); // one function symbol has only one arity.
                                        for (unsigned i=0; i<inA.size(); i++) {
                                            cell2[inA.at(i)].insert(inB.at(i));
                                        }
                                    }
                                }
                            }
                            vertex2.insert(cell2);

                            // Increment indices
                            for (auto it = B_transition_combinations.rbegin(); it != B_transition_combinations.rend(); it++) {
                                // std::cout << AUTOQ::Util::Convert::ToString(*(it->second.begin()->second.second)) << "\n";
                                // std::cout << AUTOQ::Util::Convert::ToString(*std::prev(it->second.begin()->second.first.end(), 1)) << "\n";
                                // std::cout << AUTOQ::Util::Convert::ToString(it->second.begin()->second.second) << "\n";
                                // std::cout << &*(it->second.begin()->second.second) << "\n";
                                // std::cout << &*std::next(it->second.begin()->second.second, 1) << "\n";
                                // std::cout << &*(it->second.begin()->second.first.end()) << "\n";
                                const auto &q = it->first;
                                const auto &f = it->second.begin()->first;
                                if (std::next(it->second.begin()->second, 1) != transB[q][f].end()) {
                                    it->second.begin()->second++;
                                    break;
                                } else {
                                    if (it == std::prev(B_transition_combinations.rend(), 1)) { // position equivalent to .begin()
                                        have_listed_all_combinationsB = true;
                                        break; // All combinations have been generated
                                    }
                                    it->second.begin()->second = transB[q][f].begin();
                                }
                            }
                        }
                        if (!cell_fail) { // is_leaf_vertex
                            vertex_fail = false;
                        }
                    }
                    if (is_leaf_vertex) { // only when considering some particular transitions
                        if (vertex_fail) {
                            auto stop_include = std::chrono::steady_clock::now();
                            include_status = "X";
                            return false;
                        }
                    } else if (!visited.contains(vertex2)) {
                        visited.insert(vertex2);
                        bfs.push(vertex2);
                    }
                }

                // Increment indices
                for (auto it = A_transition_combinations.rbegin(); it != A_transition_combinations.rend(); it++) {
                    const auto &qA = it->first;
                    if (std::next(it->second, 1) != transA[qA].end()) {
                        it->second = std::next(it->second, 1);
                        break;
                    } else {
                        if (it == std::prev(A_transition_combinations.rend(), 1)) { // position equivalent to .begin()
                            have_listed_all_combinationsA = true;
                            break; // All combinations have been generated
                        }
                        it->second = transA[qA].begin();
                    }
                }
            } while (!have_listed_all_combinationsA);
        }
        auto stop_include = std::chrono::steady_clock::now();
        include_status = AUTOQ::Util::Convert::toString(stop_include - start_include);
        return true;
    }

    /** checks language equivalence of two TAs */
    template <typename Symbol>
    bool AUTOQ::Automata<Symbol>::check_equal(const Automata<Symbol>& lhsPath, const Automata<Symbol>& rhsPath)
    {
    return check_inclusion(lhsPath, rhsPath) && check_inclusion(rhsPath, lhsPath);
    }

    // template <>
    // bool AUTOQ::TreeAutomata::check_equal_aut(
    //     AUTOQ::TreeAutomata lhs,
    //     AUTOQ::TreeAutomata rhs)
    // {
    // return check_equal(lhs, rhs);
    // }
// } // anonymous namespace
/******************************************************/

template <typename InitialSymbol>
void AUTOQ::Automata<InitialSymbol>::initialize_stats() {
    stateBefore = stateNum;
    transitionBefore = transition_size();
    start_execute = std::chrono::steady_clock::now();
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::execute(const char *filename) {
    initialize_stats();

    std::ifstream qasm(filename);
    const std::regex digit("\\d+");
    const std::regex_iterator<std::string::iterator> END;
    if (!qasm.is_open()) throw std::runtime_error("[ERROR] Failed to open file " + std::string(filename) + ".");
    std::string line, previous_line;
    while (getline(qasm, line)) {
        if (line.find("OPENQASM") == 0 || line.find("include ") == 0|| line.find("//") == 0) continue;
        if (line.find("qreg ") == 0) {
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
        } else if (line.find("PRINT_STATS") == 0) {
            print_stats(previous_line, true);
        } else if (line.find("PRINT_AUT") == 0) {
            print_aut();
        } else if (line.find("STOP") == 0) {
            break;
        } else if (line.length() > 0)
            throw std::runtime_error("[ERROR] unsupported gate: " + line + ".");
        previous_line = line;
        stop_execute = std::chrono::steady_clock::now();
    }
    qasm.close();
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
bool AUTOQ::is_spec_satisfied(const Constraint &C, const SymbolicAutomata &Ae, const PredicateAutomata &As) {
    using State = SymbolicAutomata::State;
    using StateSet = SymbolicAutomata::StateSet;
    using StateVector = SymbolicAutomata::StateVector;
    StateSet As_finalStates(As.finalStates.begin(), As.finalStates.end());
    std::vector<std::pair<State, StateSet>> processed; // ← ∅;
    std::queue<std::pair<State, StateSet>> worklist;
    for (const auto &te : Ae.transitions) {
        if (te.first.is_leaf()) {
            for (const auto &qe: te.second.at({})) {
                StateSet Us;
                for (const auto &ps : As.transitions) {
                    if (ps.first.is_leaf()) {
                        if (check_validity(C, ps.first.symbol(), te.first.symbol())) { // C ⇒ ps(te)
                            for (const auto &us: ps.second.at({})) {
                                Us.insert(us);
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
                            for (const auto &in_out : As.transitions.at({AUTOQ::Symbol::Predicate(alpha.symbol().complex.at(Complex::Complex::One()).at("1")), {}})) {
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
                            auto it = te.second.find({qeUs1.first, qeUs2.first});
                            if (it != te.second.end()) {
                                for (const auto &q : it->second) { // He
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

template <typename Symbol> // qubit: int, all colors: AUTOQ::Automata<Symbol>::Tag
// returns a set of trees and all colors used in each layer for each tree
std::vector<std::pair<std::map<int, typename AUTOQ::Automata<Symbol>::Tag>, std::vector<std::string>>> print(
    const AUTOQ::Automata<Symbol> &aut,
    const std::map<typename AUTOQ::Automata<Symbol>::State, std::vector<typename AUTOQ::Automata<Symbol>::SymbolTag>> &leafSymbolTagsMap,
    const std::map<int, std::map<typename AUTOQ::Automata<Symbol>::State, std::vector<typename AUTOQ::Automata<Symbol>::Tag>>> &dqCOLORs,
    int qubit, typename AUTOQ::Automata<Symbol>::State top) {
    std::vector<std::pair<std::map<int, typename AUTOQ::Automata<Symbol>::Tag>, std::vector<std::string>>> answers;
    if (qubit == static_cast<int>(aut.qubitNum + 1)) {
        for (const auto &symbol_tag : leafSymbolTagsMap.at(top)) {
            std::stringstream ss;
            ss << symbol_tag.symbol();
            answers.push_back({{{qubit, symbol_tag.tag()}}, {ss.str()}});
        }
        // std::cout << AUTOQ::Util::Convert::ToString(answers) << "\n";
        return answers;
    }
    for (const auto &tr : aut.transitions) {
        if (tr.first.symbol().is_internal() && tr.first.symbol().qubit()==qubit) {
            for (const auto &in_outs : tr.second) {
                if (in_outs.second.find(top) != in_outs.second.end()) { // the topmost transition's top state must contain "q"
                    // List all left subtrees below layer "qubit" rooted at the left child of this transition
                    auto all_left_trees = print(aut, leafSymbolTagsMap, dqCOLORs, qubit + 1, in_outs.first.at(0));
                    // List all right subtrees below layer "qubit" rooted at the right child of this transition
                    auto all_right_trees = print(aut, leafSymbolTagsMap, dqCOLORs, qubit + 1, in_outs.first.at(1));
                    for (const auto &L : all_left_trees) { // L: one left tree data structure
                        const auto &colorsL = L.first; // all used colors in each layer of L
                        for (const auto &R : all_right_trees) { // R: one right tree data structure
                            auto subtreeL = L.second; // this left subtree
                            const auto &colorsR = R.first; // all used colors in each layer of R
                            const auto &subtreeR = R.second; // this right subtree
                            std::map<int, typename AUTOQ::Automata<Symbol>::Tag> colorsLtR; // construct all newly used colors in each layer of L+R so far
                            for (const auto &kv : colorsL) { // in fact d > qubit
                                const auto d = kv.first; // in fact will loop through each layer below this layer
                                colorsLtR[d] = kv.second | colorsR.at(d); // of course union the left color"s" and the right color"s"
                                for (const auto &qCOL : dqCOLORs.at(d)) { // inspect all top states q used in this layer
                                    // and check if there are at least two transitions under this q included in colorsLtR[d]
                                    // if yes, then fail (this LR cannot be used in the future).
                                    int count = 0;
                                    for (const auto &color : qCOL.second) { // loop through all transitions
                                        count += (colorsLtR[d] == (colorsLtR[d] | color)); // color is included in colorsLtR[d]
                                        if (count >= 2) goto FAIL;
                                    }
                                }
                            }
                            // so far has merged all used colors in L+R so far
                            colorsLtR[qubit] |= tr.first.tag(); // now we want to add the color of the used transition in this layer
                            for (const auto &qCOL : dqCOLORs.at(qubit)) { // inspect all top states q used in this layer
                                // and check if there are at least two transitions under this q included in colorsLtR[qubit]
                                // if yes, then fail (this LtR cannot be used in the future).
                                int count = 0;
                                for (const auto &color : qCOL.second) { // loop through all transitions
                                    count += (colorsLtR[qubit] == (colorsLtR[qubit] | color)); // color is included in colorsLtR[qubit]
                                    if (count >= 2) goto FAIL;
                                }
                            }
                            subtreeL.insert(subtreeL.end(), subtreeR.begin(), subtreeR.end());
                            answers.push_back({colorsLtR, subtreeL}); // now subtreeL actually becomes subtreeLtR
                            FAIL: {}
                        }
                    }
                }
            }
        }
    }
    // std::cout << AUTOQ::Util::Convert::ToString(answers) << "\n";
    return answers;
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::print_language(const char *str) const {
    std::cout << str;
    std::map<State, std::vector<SymbolTag>> leafSymbolTagsMap;
    std::map<int, std::map<State, std::vector<Tag>>> dqCOLORs;
    for (const auto &t : transitions) {
        for (const auto &in_outs : t.second) { // construct the map from state to leaf symbols
            for (const auto &q : in_outs.second) {
                if (t.first.symbol().is_internal())
                    dqCOLORs[static_cast<int>(t.first.symbol().qubit())][q].push_back(t.first.tag());
                else
                    dqCOLORs[qubitNum+1][q].push_back(t.first.tag());
            }
        }
        if (t.first.is_leaf()) { // construct the map from state to leaf symbols
            for (const auto &s : t.second.at({})) {
                leafSymbolTagsMap[s].push_back(t.first);
            }
        }
    }
    std::set<std::vector<std::string>> result_trees;
    for (const auto &s : finalStates) {
        auto results = print(*this, leafSymbolTagsMap, dqCOLORs, 1, s); // many accepted trees
        for (const auto& pair : results) {
            result_trees.insert(pair.second);
        }
    }
    for (const auto &tree : result_trees) { // each result is a tree
        std::map<std::string, int> count;
        for (unsigned i=0; i<tree.size(); i++)
            count[tree[i]]++;
        auto ptr = std::max_element(count.begin(), count.end(), [](const auto &x, const auto &y) {
            return x.second < y.second;
        });
        for (unsigned i=0; i<tree.size(); i++) {
            if (tree[i] != (ptr->first))
                std::cout << boost::dynamic_bitset(qubitNum, i) << ":" << tree[i] << " ";
        }
        std::cout << "*:" << (ptr->first) << std::endl;
    }
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::print_stats(const std::string &str, bool newline) {
    state_renumbering();
    std::cout << str;
    std::cout << AUTOQ::Util::Convert::ToString(qubitNum) << " & " << AUTOQ::TreeAutomata::gateCount
              << " & " << stateBefore << " & " << stateNum
              << " & " << transitionBefore << " & " << transition_size()
              << " & " << AUTOQ::Util::Convert::toString(stop_execute - start_execute) << " & " << include_status;
    if (newline)
        std::cout << std::endl;
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;