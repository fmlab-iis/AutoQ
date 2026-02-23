/**
 * Shared helpers for automata reduction: reindexing, compaction, single-occurrence check.
 * Used by reduce.cc (light/bottom-up/remove_useless) and reduce_sim.cc (sim_reduce).
 */
#ifndef AUTOQ_REDUCE_COMMON_HH
#define AUTOQ_REDUCE_COMMON_HH

#include "autoq/aut_description.hh"
#include "autoq/simulation/transl_weak.hh"
#include <unordered_map>
#include <set>
#include <algorithm>

namespace AUTOQ {
namespace reduce_detail {

template <class Index, typename Symbol>
void reindex_aut_states(Automata<Symbol>& aut, Index& index)
{
  using State = typename Automata<Symbol>::State;
  using StateVector = typename Automata<Symbol>::StateVector;

  StateVector newFinal;
  for (const State& state : aut.finalStates) {
    if (newFinal.end() == std::find(newFinal.begin(), newFinal.end(), index[state])) {
      newFinal.push_back(index[state]);
    }
  }
  typename Automata<Symbol>::TopDownTransitions transitions_new;
  for (const auto &t : aut.transitions) {
    for (const auto &out_ins : t.second) {
      const auto &out = out_ins.first;
      for (auto in : out_ins.second) {
        for (auto &e : in) {
          e = index[e];
        }
        transitions_new[t.first][index[out]].insert(in);
      }
    }
  }
  aut.finalStates = newFinal;
  aut.transitions = transitions_new;
}

template <class T>
int find_index(const std::vector<T> &arr, T item) {
  for (int i = 0; i < static_cast<int>(arr.size()); ++i) {
    if (arr[i] == item)
      return i;
  }
  std::__throw_out_of_range("[ERROR] find_index: item not found.");
}

/// Checks that a state is at most once on the right-hand (parent) side of any rule.
template <typename Symbol>
bool aut_is_single_occurrence(const Automata<Symbol>& aut)
{
  using State = typename Automata<Symbol>::State;
  std::set<State> occurrences;
  for (auto symbMapPair : aut.transitions) {
    for (auto vecSetPair : symbMapPair.second) {
      for (auto state : vecSetPair.second) {
        auto itBoolPair = occurrences.insert(state);
        if (!itBoolPair.second) { return false; }
      }
    }
  }
  return true;
}

/// Makes a TA compact (states renumbered from 0 consecutively).
template <typename Symbol>
void compact_aut(Automata<Symbol>& aut)
{
  using State = typename Automata<Symbol>::State;
  using StateToStateMap = std::unordered_map<State, State>;
  using StateToStateTranslWeak = Util::TranslatorWeak<StateToStateMap>;
  StateToStateMap translMap;
  size_t stateCnt = 0;
  StateToStateTranslWeak transl(translMap,
      [&stateCnt](const State&) {return stateCnt++;});
  reindex_aut_states(aut, transl);
  aut.stateNum = stateCnt;
}

}  // namespace reduce_detail
}  // namespace AUTOQ

#endif
