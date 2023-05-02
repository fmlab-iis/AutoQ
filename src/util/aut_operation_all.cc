#include <autoq/util/aut_description.hh>
#include <autoq/serialization/timbuk_serializer.hh>

#include "simulation/explicit_lts.hh"

using namespace AUTOQ;
using namespace AUTOQ::Util;
using AUTOQ::Serialization::TimbukSerializer;

namespace { // anonymous namespace

  template <class Index, typename InitialSymbol>
  ExplicitLTS translate_to_lts_downward(
    const Automata<InitialSymbol>& aut,
    size_t              numStates,
    Index&              stateIndex)
  {
    using State = typename Automata<InitialSymbol>::State;
    using Symbol = typename Automata<InitialSymbol>::Symbol;
    using StateVector = typename Automata<InitialSymbol>::StateVector;

    std::unordered_map<Symbol, size_t> symbolMap;
    std::unordered_map<const StateVector*, size_t> lhsMap;

    size_t symbolCnt = 0;
    Util::TranslatorWeak2<std::unordered_map<Symbol, size_t>>
      symbolTranslator(symbolMap, [&symbolCnt](const Symbol&){ return symbolCnt++; });

    size_t lhsCnt = numStates;
    Util::TranslatorWeak2<std::unordered_map<const StateVector*, size_t>>
      lhsTranslator(lhsMap, [&lhsCnt](const StateVector*){ return lhsCnt++; });

    ExplicitLTS result(numStates);

    // start with getting translation for final states
    for (const State& finState : aut.finalStates) {
      stateIndex[finState];
    }

    // Iterate through all transitions and adds them to the LTS.
    for (const auto& symMap : aut.transitions) {
      const auto& symbolName = symbolTranslator(symMap.first);

      for (const auto& vecSet : symMap.second) {
        const auto& tuple = vecSet.first;

        for (const auto& parent : vecSet.second) {
          const auto& parentName = stateIndex[parent];

          size_t dest;
          if (1 == tuple.size())
          { // a(p) -> q ... inline lhs of size 1 >:-)
            dest = stateIndex[tuple.front()];
            assert(dest < numStates);
          } else
          { // a(p,r) -> q
            dest = lhsTranslator(&tuple);
          }

          result.addTransition(parentName, symbolName, dest);
        }
      }
    }

    for (auto& tupleIndexPair : lhsMap)
    {	// for n-ary transition (n > 1), decompose the hyperedge into n ordinary
      // edges
      assert(tupleIndexPair.first);

      size_t i = 0;
      for (auto& state : *tupleIndexPair.first) {
        size_t dest = stateIndex[state];
        assert(dest < numStates);

        result.addTransition(tupleIndexPair.second, symbolMap.size() + i, dest);
        ++i;
      }
    }

    result.init();

    return result;
  }

  template <typename InitialSymbol>
  size_t count_aut_states(const AUTOQ::Util::Automata<InitialSymbol>& aut)
  {
    using State = typename Automata<InitialSymbol>::State;

    std::set<State> states;
    for (const auto& state : aut.finalStates) {
      states.insert(state);
    }

    for (const auto& symMap : aut.transitions) {
      for (const auto& vecSet : symMap.second) {
        states.insert(vecSet.second.begin(), vecSet.second.end());
        for (const auto& child : vecSet.first) {
          states.insert(child);
        }
      }
    }

    return states.size();
  }

  template <typename InitialSymbol>
  typename Util::DiscontBinaryRelation<typename Automata<InitialSymbol>::State> compute_down_sim(const AUTOQ::Util::Automata<InitialSymbol>& aut)
  {
    using State = typename Automata<InitialSymbol>::State;
    using StateToIndexMap = typename std::unordered_map<State, size_t>;
    using StateToIndexTranslWeak = typename Util::TranslatorWeak<StateToIndexMap>;
    using DiscontBinaryRelOnStates = typename Util::DiscontBinaryRelation<State>;

    StateToIndexMap translMap;
    size_t stateCnt = 0;
    StateToIndexTranslWeak transl(translMap,
        [&stateCnt](const State&) {return stateCnt++;});

    size_t num_states = count_aut_states(aut);
    ExplicitLTS lts = translate_to_lts_downward(aut, num_states, transl);
    BinaryRelation ltsSim = lts.computeSimulation(num_states);
    return DiscontBinaryRelOnStates(ltsSim, translMap);
  }

  template <class Index, typename InitialSymbol>
  void reindex_aut_states(Automata<InitialSymbol>& aut, Index& index)
  {
    using State = typename Automata<InitialSymbol>::State;
    using StateSet = typename Automata<InitialSymbol>::StateSet;
    using StateVector = typename Automata<InitialSymbol>::StateVector;
    using TransitionMap = typename Automata<InitialSymbol>::TransitionMap;

    StateVector newFinal;
    TransitionMap newTrans;

    for (const State& state : aut.finalStates) { // process final states
      if (newFinal.end() == std::find(newFinal.begin(), newFinal.end(), index[state])) {
        newFinal.push_back(index[state]);
      }
    }

    // Iterate through all transitions and add reindex everything
    for (const auto& symMap : aut.transitions) {
      const auto& symbol = symMap.first;

      std::map<StateVector, StateSet> newMap;

      for (const auto& vecSet : symMap.second) {
        const auto& tuple = vecSet.first;
        StateVector newTuple;
        for (const auto& child : tuple) {
          newTuple.push_back(index[child]);
        }

        StateSet newSet;
        for (const auto& parent : vecSet.second) {
          newSet.insert(index[parent]);
        }

        auto itBoolPair = newMap.insert({newTuple, newSet});
        if (!itBoolPair.second) { // there is already something
            StateSet& ss = itBoolPair.first->second;
            ss.insert(newSet.begin(), newSet.end());
        }
      }

      newTrans.insert({symbol, newMap});
    }

    aut.finalStates = newFinal;
    aut.transitions = newTrans;
  }

  template <class T>
  int findIndex(const std::vector<T> &arr, T item) {
      for (int i = 0; i < static_cast<int>(arr.size()); ++i) {
          if (arr[i] == item)
              return i;
      }
      std::__throw_out_of_range("[ERROR] findIndex: item not found.");
  }

  /// Checks that a state is at most once on the right-hand (parent) side of
  /// any rule.
  template <typename InitialSymbol>
  bool aut_is_single_occurrence(const Automata<InitialSymbol>& aut)
  {
    using State = typename Automata<InitialSymbol>::State;

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

  // Makes a TA compact (states are renumbered to start from 0 and go consecutively up
  template <typename InitialSymbol>
  void compact_aut(Automata<InitialSymbol>& aut)
  {
    using State = typename Automata<InitialSymbol>::State;
    using StateToStateMap = typename std::unordered_map<State, State>;
    using StateToStateTranslWeak = typename Util::TranslatorWeak<StateToStateMap>;
    StateToStateMap translMap;
    size_t stateCnt = 0;
    StateToStateTranslWeak transl(translMap,
        [&stateCnt](const State&) {return stateCnt++;});

    // AUTOQ_DEBUG("Before compact stateNum = " + Convert::ToString(aut.stateNum));
    reindex_aut_states(aut, transl);
    aut.stateNum = stateCnt;
    // AUTOQ_DEBUG("After compact stateNum = " + Convert::ToString(aut.stateNum));
  }
} // anonymous namespace

template <typename InitialSymbol>
bool AUTOQ::Util::Automata<InitialSymbol>::light_reduce_up()
{
  using State = typename Automata<InitialSymbol>::State;
  using StateToStateMap = typename std::unordered_map<State, State>;

  StateToStateMap index;
  for (const auto& symbMapPair : this->transitions) {
    for (const auto& vecSetPair : symbMapPair.second) {
      for (auto state : vecSetPair.second) {
        auto itBoolPair = index.insert({state, *vecSetPair.second.begin()});
        if (!itBoolPair.second) { // if there was more than one occurrence of 'state' as parent
          itBoolPair.first->second = state;
        }
      }
    }
  }

  bool changed = false;
  for (const auto& statePair : index) { // detect if there was some change
    if (statePair.first != statePair.second) {
      changed = true;
      break;
    }
  }

  // AUTOQ_DEBUG("index: " + Convert::ToString(index));
  if (changed) {
    // Automata old = *this;
    reindex_aut_states(*this, index);
    // assert(check_equal_aut(old, *this));
  }

  return changed;
}

template <typename InitialSymbol>
bool AUTOQ::Util::Automata<InitialSymbol>::light_reduce_up_iter()
{
  size_t iterations = 0;
  bool changed = true;
  while (changed) {
    changed = this->light_reduce_up();
    ++iterations;
  }

  return 1 == iterations;
}

template <typename InitialSymbol>
bool AUTOQ::Util::Automata<InitialSymbol>::light_reduce_down()
{
  using State = typename Automata<InitialSymbol>::State;
  using StateToStateMap = typename std::unordered_map<State, State>;
  using StateToStateTranslWeak = typename Util::TranslatorWeak<StateToStateMap>;

  // AUTOQ_DEBUG("aut:\n" + this->ToString());
  std::list<std::set<State>> partition;
  std::map<State, std::set<State>*> state_to_class;

  // first process root states
  std::set<State> class_candidate(this->finalStates.begin(), this->finalStates.end());
  for (const auto& symbMapPair : this->transitions) {
    const auto& vector_map = symbMapPair.second;
    for (const auto& vecSetPair : vector_map) {
      const auto& children = vecSetPair.first;
      for (const auto& child : children) {
        if (class_candidate.end() != class_candidate.find(child)) {
          assert(false);
        }
      }
    }
  }

  if (class_candidate.size() > 1) {
    StateToStateMap index;
    for (auto state : class_candidate) {
      index.insert({state, *class_candidate.begin()});
    }

    StateToStateTranslWeak transl(index, [](const State& state) {return state;});

    reindex_aut_states(*this, transl);
    return true;
  }

  // then process other states
  for (const auto& symbMapPair : this->transitions) {
    const auto& vector_map = symbMapPair.second;
    std::map<State, std::set<StateVector>> top_down_map;
    for (const auto& vecSetPair : vector_map) {
      const auto& state_vector = vecSetPair.first;
      const auto& parent_states = vecSetPair.second;
      for (auto parent : parent_states) {
        auto itBoolPair = top_down_map.insert({parent, {state_vector}});
        if (!itBoolPair.second) { // 'parent' already mapped
          itBoolPair.first->second.insert(state_vector);
        }
      }
    }
    // AUTOQ_DEBUG("top down map: " + Convert::ToString(top_down_map));

    for (const auto& parentSetPair : top_down_map) {
      const auto& childrenSet = parentSetPair.second;
      std::map<State, std::set<State>> left_child_map;
      std::map<State, std::set<State>> right_child_map;

      for (const auto& state_vector : childrenSet) {
        if (2 != state_vector.size()) {
          assert(0 == state_vector.size());
          continue;
        }

        auto itBoolPair = left_child_map.insert({state_vector[0], {state_vector[1]}});
        if (!itBoolPair.second) { // if no insertion happened
          itBoolPair.first->second.insert(state_vector[1]);
        }
        itBoolPair = right_child_map.insert({state_vector[1], {state_vector[0]}});
        if (!itBoolPair.second) { // if no insertion happened
          itBoolPair.first->second.insert(state_vector[0]);
        }
      }
      // AUTOQ_DEBUG("left child map: " + Convert::ToString(left_child_map));
      // AUTOQ_DEBUG("right child map: " + Convert::ToString(right_child_map));

      StateToStateMap index;

      for (auto stateSetPair : left_child_map) {
        const auto& state = stateSetPair.first;
        const auto& left_map_state_set = stateSetPair.second;
        if (1 == left_map_state_set.size()) { continue; }
        if (left_map_state_set == right_child_map[state]) { // interesting case
          const auto& class_cand = left_map_state_set;
          for (const auto& st2 : class_cand) {
            index.insert({st2, *class_cand.begin()});
          }
        }

        if (!index.empty()) {
          // AUTOQ_DEBUG("index: " + Convert::ToString(index));
          // TODO: assert here something
          //
          // check sanity
          bool sane = true;
          for (const auto& symbMapPair : this->transitions) {
            const auto& vector_map = symbMapPair.second;
            if (!sane) { break; }
            for (const auto& vecSetPair : vector_map) {
              const auto& vec = vecSetPair.first;
              if (2 == vec.size()) {
                if ((left_map_state_set.end() != left_map_state_set.find(vec[0]) &&
                     vec[1] != state) ||
                    (left_map_state_set.end() != left_map_state_set.find(vec[1]) &&
                     vec[0] != state)
                   ) {
                  sane = false;
                //   AUTOQ_DEBUG("Sanity check in downward light reduction failed, not reducing!");
                  break;
                }

              } else {
                assert(0 == vec.size());
              }
            }
          }

          if (!sane) { // if some sanity check failed
            index = StateToStateMap();
            continue;
          }

          StateToStateTranslWeak transl(index, [](const State& state) { return state; });
          reindex_aut_states(*this, transl);
          return true;
        }
      }
    }
  }

  return false;
}

template <typename InitialSymbol>
bool AUTOQ::Util::Automata<InitialSymbol>::light_reduce_down_iter()
{
  size_t iterations = 0;
  bool changed = true;
  while (changed) {
    changed = this->light_reduce_down();
    ++iterations;
  }

  return 1 == iterations;
}

template <typename InitialSymbol>
int AUTOQ::Util::Automata<InitialSymbol>::count_transitions() {
    int count = 0;
    for (const auto &t : transitions)
        for (const auto &in_outs : t.second) {
            count += in_outs.second.size();
        }
    return count;
}

template <typename InitialSymbol>
void AUTOQ::Util::Automata<InitialSymbol>::reduce() {
    auto start = std::chrono::steady_clock::now();
    // AUTOQ_DEBUG("before light_reduce_down: " + Convert::ToString(count_aut_states(*this)));
    // this->sim_reduce();
    this->light_reduce_up_iter();

    Automata old = *this;
    this->light_reduce_down_iter();
    // AUTOQ_DEBUG("after light_reduce_down: " + Convert::ToString(count_aut_states(*this)));

    compact_aut(*this);
    // assert(check_equal_aut(old, *this));

    auto duration = std::chrono::steady_clock::now() - start;
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename InitialSymbol>
AUTOQ::Util::Automata<InitialSymbol> AUTOQ::Util::Automata<InitialSymbol>::Union(const Automata<InitialSymbol> &o) {
    if (*this == Automata<InitialSymbol>()) return o;

    Automata<InitialSymbol> result;
    result = *this;
    result.name = "Union";
    if (result.qubitNum != o.qubitNum) {
        throw std::runtime_error("Two automata of different numbers of qubits cannot be unioned together.");
    }
    result.stateNum += o.stateNum;
    // TODO: How to check if the two input automata have different k's?

    for (const auto &t : o.transitions) {
        auto &container = result.transitions[t.first];
        for (const auto &in_outs : t.second) {
            auto in = in_outs.first;
            for (unsigned i=0; i<in.size(); i++) {
                in[i] += this->stateNum;
            }
            auto &container_out = container[in];
            const auto &outs = in_outs.second;
            for (const auto &s : outs) {
                container_out.insert(s + this->stateNum);
            }
        }
    }
    result.finalStates.reserve(finalStates.size() + o.finalStates.size()); // TODO: Can we set the initial capacity?
    for (const auto &s : o.finalStates) {
        result.finalStates.push_back(s + this->stateNum);
    }
    result.reduce();
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
    return result;
}

template <typename InitialSymbol>
void AUTOQ::Util::Automata<InitialSymbol>::print() {
    std::cout << AUTOQ::Serialization::TimbukSerializer::Serialize(*this);
}

template <typename InitialSymbol>
int AUTOQ::Util::Automata<InitialSymbol>::transition_size() {
    int answer = 0;
    for (const auto &t : transitions) {
        for (const auto &in_out : t.second) {
            answer += in_out.second.size();
        }
    }
    return answer;
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Util::Automata<AUTOQ::Util::Concrete>;
template struct AUTOQ::Util::Automata<AUTOQ::Util::Symbolic>;
template struct AUTOQ::Util::Automata<AUTOQ::Util::Predicate>;