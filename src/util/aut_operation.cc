#include <autoq/aut_description.hh>
#include <autoq/complex/complex.hh>
#include <autoq/symbol/index.hh>
#include <autoq/symbol/concrete.hh>
#include <autoq/symbol/symbolic.hh>
#include <autoq/symbol/predicate.hh>
#include <autoq/util/util.hh>
#include <autoq/inclusion.hh>
#include <autoq/parsing/complex_parser.hh>
#include <autoq/serialization/timbuk_serializer.hh>

#include "simulation/explicit_lts.hh"

#include <fstream>
#include <numeric>
#include <chrono>
#include <queue>
#include <regex>
#include <bit>
#include <boost/dynamic_bitset.hpp>
#include <z3++.h>

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


// template <typename Symbol>
// void AUTOQ::Automata<Symbol>::remove_impossible_colors() {
//     std::map<State, std::map<Tag, std::vector<std::pair<Symbol, StateVector>>>> qcfi;
//     for (const auto &tr : transitions) {
//         auto &symbol_tag = tr.first;
//         auto &in_outs = tr.second;
//         for (const auto &in_out : in_outs) {
//             auto &in = in_out.first;
//             auto &outs = in_out.second;
//             for (const auto &out : outs) {
//                 qcfi[out][symbol_tag.tag()].push_back({symbol_tag.symbol(), in});
//             }
//         }
//     }

//     std::map<State, std::set<Tag>> delete_colors;
//     for (const auto &q_ : qcfi) {
//         for (auto c_ptr = q_.second.rbegin(); c_ptr != q_.second.rend(); ++c_ptr) {
//             if (c_ptr->second.size() >= 2) {
//                 delete_colors[q_.first].insert(c_ptr->first);
//             }
//             else {
//                 for (auto c_ptr2 = q_.second.begin(); c_ptr2 != q_.second.end(); ++c_ptr2) {
//                     if (c_ptr2->first >= c_ptr->first) break;
//                     if ((c_ptr->first | c_ptr2->first) == c_ptr->first) {
//                         delete_colors[q_.first].insert(c_ptr->first);
//                         break;
//                     }
//                 }
//             }
//         }
//     }

//     for (const auto &q_ : delete_colors) {
//         for (const auto &c : q_.second) {
//             std::vector<std::pair<Symbol, StateVector>> to_be_deleted;
//             for (auto &fc_iq : transitions) {
//                 if (fc_iq.first.tag() == c) {
//                     for (auto &in_outs : fc_iq.second) {
//                         in_outs.second.erase(q_.first);
//                         if (in_outs.second.empty())
//                             to_be_deleted.push_back({fc_iq.first.symbol(), in_outs.first});
//                     }
//                 }
//             }
//             for (const auto &f_i : to_be_deleted)
//                 transitions[{f_i.first, c}].erase(f_i.second);
//         }
//     }

//     for (auto &tr : transitions) {
//         auto &symbol_tag = tr.first;
//         auto &in_outs = tr.second;
//         for (auto &in_out : in_outs) {
//             auto &in = in_out.first;
//             auto &outs = in_out.second;
//             if (outs.empty()) {
//                 in_outs.erase(in);
//             }
//         }
//         if (in_outs.empty())
//             transitions.erase(symbol_tag);
//     }
// }

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
    StateVector finalStates_new;
    for (const auto &s : finalStates) {
        if (traversed[s])
            finalStates_new.push_back(s);
    }
    finalStates = finalStates_new;

    /*********************
     * Part 3: Renumbering
     *********************/
    state_renumbering();
    auto duration = std::chrono::steady_clock::now() - start;
    total_removeuseless_time += duration;
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
//                     transitions[s][n + num_of_states].insert({{}}); // duplicate this leaf transition
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
//                     transitions[symbol_tag.symbol()][v].insert(in_out.first); // modify
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
//                         result.transitions[{symbol, it->first.tag()}][i].insert({{}});
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
            for (const auto &out_ins : tr.second) {
                if (out_ins.first == top) { // the topmost transition's top state must contain "q"
                    for (const auto &in : out_ins.second) {
                        // List all left subtrees below layer "qubit" rooted at the left child of this transition
                        auto all_left_trees = print(aut, leafSymbolTagsMap, dqCOLORs, qubit + 1, in.at(0));
                        // List all right subtrees below layer "qubit" rooted at the right child of this transition
                        auto all_right_trees = print(aut, leafSymbolTagsMap, dqCOLORs, qubit + 1, in.at(1));
                        for (const auto &L : all_left_trees) { // L: one left tree data structure
                            const auto &colorsL = L.first; // all used colors in each layer of L
                            for (const auto &R : all_right_trees) { // R: one right tree data structure
                                auto subtreeL = L.second; // this left subtree
                                const auto &colorsR = R.first; // all used colors in each layer of R
                                const auto &subtreeR = R.second; // this right subtree
                                std::map<int, typename AUTOQ::Automata<Symbol>::Tag> colorsLtR; // construct all newly used colors in each layer of L+R so far
                                for (const auto &kv : colorsL) { // in fact d > qubit
                                    const auto d = kv.first; // in fact will loop through each layer below this layer
                                    colorsLtR[d] = kv.second & colorsR.at(d); // of course union the left color"s" and the right color"s"
                                    if (colorsLtR[d] == 0)
                                        goto FAIL;
                                    // for (const auto &qCOL : dqCOLORs.at(d)) { // inspect all top states q used in this layer
                                    //     // and check if there are at least two transitions under this q included in colorsLtR[d]
                                    //     // if yes, then fail (this LR cannot be used in the future).
                                    //     int count = 0;
                                    //     for (const auto &color : qCOL.second) { // loop through all transitions
                                    //         count += (colorsLtR[d] == (colorsLtR[d] | color)); // color is included in colorsLtR[d]
                                    //         if (count >= 2) goto FAIL;
                                    //     }
                                    // }
                                }
                                // so far has merged all used colors in L+R so far
                                colorsLtR[qubit] = tr.first.tag(); // now we want to add the color of the used transition in this layer
                                if (colorsLtR[qubit] == 0)
                                    goto FAIL;
                                // for (const auto &qCOL : dqCOLORs.at(qubit)) { // inspect all top states q used in this layer
                                //     // and check if there are at least two transitions under this q included in colorsLtR[qubit]
                                //     // if yes, then fail (this LtR cannot be used in the future).
                                //     int count = 0;
                                //     for (const auto &color : qCOL.second) { // loop through all transitions
                                //         count += (colorsLtR[qubit] == (colorsLtR[qubit] | color)); // color is included in colorsLtR[qubit]
                                //         if (count >= 2) goto FAIL;
                                //     }
                                // }
                                subtreeL.insert(subtreeL.end(), subtreeR.begin(), subtreeR.end());
                                answers.push_back({colorsLtR, subtreeL}); // now subtreeL actually becomes subtreeLtR
                                FAIL: {}
                            }
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
        for (const auto &out_ins : t.second) { // construct the map from state to leaf symbols
            const auto &q = out_ins.first;
            if (t.first.symbol().is_internal())
                dqCOLORs[static_cast<int>(t.first.symbol().qubit())][q].push_back(t.first.tag());
            else
                dqCOLORs[qubitNum+1][q].push_back(t.first.tag());
        }
        if (t.first.is_leaf()) { // construct the map from state to leaf symbols
            for (const auto &out_ins : t.second) {
                const auto &s = out_ins.first;
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

template <typename Symbol>
void AUTOQ::Automata<Symbol>::unfold_top() {
    TransitionMap transitions_insert;
    std::map<SymbolTag, std::vector<StateVector>> transitions_delete;
    for (const auto &fc_ois : transitions) {
        const auto &fc = fc_ois.first;
        const auto &ois = fc_ois.second;
        auto &transitions_insert_fc = transitions_insert[fc];
        auto &transitions_insert_fc2 = fc.symbol().is_internal() ? transitions_insert[{fc.symbol().qubit()+1, fc.second}] : transitions_insert_fc;
        auto &transitions_delete_fc = transitions_delete[fc];
        for (const auto &oi : ois) {
            const auto &top = oi.first;
            const auto &ins = oi.second;
            if (fc.symbol().is_leaf()) {
                transitions_insert_fc[top + stateNum].insert({{}});
            } else if (fc.symbol().qubit() == qubitNum+1) {
                auto &transitions_insert_fc_top = transitions_insert_fc[top];
                auto &transitions_insert_fc2_top_stateNum = transitions_insert_fc2[top + stateNum];
                for (auto in : ins) {
                    transitions_delete_fc.push_back(in);
                    for_each(in.begin(), in.end(), [this](auto &n) { n += stateNum; });
                    transitions_insert_fc2_top_stateNum.insert(in);
                    transitions_insert_fc_top.insert(in);
                }
            }
        }
    }
    for (const auto &fc_ins : transitions_delete) {
        const auto &fc = fc_ins.first;
        const auto &ins = fc_ins.second;
        for (auto &ois : transitions[fc]) {
            auto &oissecond = ois.second;
            for (const auto &in : ins) {
                oissecond.erase(in);
            }
        }
    }
    for (const auto &fc_ois : transitions_insert) {
        const auto &fc = fc_ois.first;
        const auto &ois = fc_ois.second;
        auto &transitions_fc = transitions[fc];
        for (const auto &oi : ois) {
            const auto &out = oi.first;
            const auto &ins = oi.second;
            transitions_fc[out].insert(ins.begin(), ins.end());
        }
    }
    stateNum *= 2;
    qubitNum++;
    remove_useless();
    reduce();
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::unfold_bottom() {
    TransitionMap transitions_result;
    for (const auto &fc_ois : transitions) {
        const auto &fc = fc_ois.first;
        const auto &ois = fc_ois.second;
        auto &transitions_result_fc = transitions_result[fc];
        auto &transitions_result_fc_shift = fc.first.is_internal() ? transitions_result[{fc.first.qubit(), fc.second << 2}] : transitions_result_fc; // TODO: temporary solution
        auto &transitions_result_shift = fc.first.is_internal() ? transitions_result[{fc.first.qubit() + 1, fc.second}] : transitions_result_fc;
        for (const auto &oi : ois) {
            const auto &top = oi.first;
            const auto &ins = oi.second;
            if (fc.first.is_leaf()) {
                transitions_result_fc[top].insert(ins.begin(), ins.end());
            } else { // internal
                if (fc.first.qubit() == 1) {
                    auto &ref = transitions_result_fc_shift[top + stateNum];
                    for (auto in : ins) {
                        for_each(in.begin(), in.end(), [this](auto &n) { n += stateNum; });
                        ref.insert(in);
                    }
                    transitions_result_shift[top + stateNum].insert(ins.begin(), ins.end());
                } else {
                    transitions_result_shift[top].insert(ins.begin(), ins.end());
                }
            }
        }
    }
    transitions = transitions_result;
    for (unsigned i=0; i<finalStates.size(); i++)
        finalStates.at(i) += stateNum;
    stateNum *= 2;
    qubitNum++;
    remove_useless();
    reduce();
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::fold() {
    TransitionMap transitions_result;
    for (const auto &fc_ois : transitions) {
        const auto &fc = fc_ois.first;
        const auto &ois = fc_ois.second;
        auto &transitions_result_fc = transitions_result[fc];
        auto &transitions_result_fc2 = transitions_result[{1, fc.second}];
        for (const auto &oi : ois) {
            const auto &top = oi.first;
            const auto &ins = oi.second;
            if (fc.first.is_internal())
                transitions_result_fc2[top].insert(ins.begin(), ins.end());
            else
                transitions_result_fc[top].insert(ins.begin(), ins.end());
        }
    }
    transitions = transitions_result;
    qubitNum = 0;
    remove_useless();
    reduce();
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;