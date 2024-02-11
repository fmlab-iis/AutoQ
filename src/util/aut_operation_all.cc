#include <autoq/symbol/concrete.hh>
#include <autoq/symbol/symbolic.hh>
#include <autoq/symbol/predicate.hh>
#include <autoq/aut_description.hh>
#include <autoq/serialization/timbuk_serializer.hh>
#include <boost/dynamic_bitset.hpp> // used in print_language

#include "simulation/explicit_lts.hh"

using namespace AUTOQ;
using namespace AUTOQ::Util;
using AUTOQ::Serialization::TimbukSerializer;

namespace { // anonymous namespace

  template <class Index, typename Symbol>
  ExplicitLTS translate_to_lts_downward(
    const Automata<Symbol>& aut,
    size_t              numStates,
    Index&              stateIndex)
  {
    using State = typename Automata<Symbol>::State;
    using SymbolTag = typename Automata<Symbol>::SymbolTag;
    using StateVector = typename Automata<Symbol>::StateVector;

    std::unordered_map<SymbolTag, size_t> symbolMap;
    std::unordered_map<const StateVector*, size_t> lhsMap;

    size_t symbolCnt = 0;
    Util::TranslatorWeak2<std::unordered_map<SymbolTag, size_t>>
      symbolTranslator(symbolMap, [&symbolCnt](const SymbolTag&){ return symbolCnt++; });

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
        const auto& parent = vecSet.first;

        for (const auto& tuple : vecSet.second) {
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

  template <typename Symbol>
  size_t count_aut_states(const AUTOQ::Automata<Symbol>& aut)
  {
    using State = typename Automata<Symbol>::State;

    std::set<State> states;
    for (const auto& state : aut.finalStates) {
      states.insert(state);
    }

    for (const auto& symMap : aut.transitions) {
      for (const auto& out_ins : symMap.second) {
        states.insert(out_ins.first);
        for (const auto& in : out_ins.second) {
            for (const auto& child : in)
                states.insert(child);
        }
      }
    }

    return states.size();
  }

  template <typename Symbol>
  typename Util::DiscontBinaryRelation<typename Automata<Symbol>::State> compute_down_sim(const AUTOQ::Automata<Symbol>& aut)
  {
    using State = typename Automata<Symbol>::State;
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

  template <class Index, typename Symbol>
  void reindex_aut_states(Automata<Symbol>& aut, Index& index)
  {
    using State = typename Automata<Symbol>::State;
    using StateSet = typename Automata<Symbol>::StateSet;

    StateSet newFinal;

    for (const State& state : aut.finalStates) { // process final states
        newFinal.insert(index[state]);
    }
    typename Automata<Symbol>::TransitionMap transitions_new;
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
  int findIndex(const std::vector<T> &arr, T item) {
      for (int i = 0; i < static_cast<int>(arr.size()); ++i) {
          if (arr[i] == item)
              return i;
      }
      std::__throw_out_of_range((AUTOQ_LOG_PREFIX + "[ERROR] findIndex: item not found.").c_str());
  }

  /// Checks that a state is at most once on the right-hand (parent) side of
  /// any rule.
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

  // Makes a TA compact (states are renumbered to start from 0 and go consecutively up
  template <typename Symbol>
  void compact_aut(Automata<Symbol>& aut)
  {
    using State = typename Automata<Symbol>::State;
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

template <typename Symbol>
bool AUTOQ::Automata<Symbol>::light_reduce_up()
{
  using State = typename Automata<Symbol>::State;
  using StateSet = typename Automata<Symbol>::StateSet;
  using StateVector = typename Automata<Symbol>::StateVector;
  using StateToStateMap = typename std::unordered_map<State, State>;

  StateToStateMap index;
  for (const auto& symbMapPair : this->transitions) {
    std::map<StateVector, StateSet> vecSetPairs;
    for (const auto& out_ins : symbMapPair.second) {
        const auto &out = out_ins.first;
        for (const auto& in : out_ins.second) {
            vecSetPairs[in].insert(out);
        }
    }
    for (const auto& vecSetPair : vecSetPairs) {
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

template <typename Symbol>
bool AUTOQ::Automata<Symbol>::light_reduce_up_iter()
{
  size_t iterations = 0;
  bool changed = true;
  while (changed) {
    changed = this->light_reduce_up();
    ++iterations;
  }

  return 1 == iterations;
}

template <typename Symbol>
bool AUTOQ::Automata<Symbol>::light_reduce_down()
{
  using State = typename Automata<Symbol>::State;
  using StateToStateMap = typename std::unordered_map<State, State>;
  using StateToStateTranslWeak = typename Util::TranslatorWeak<StateToStateMap>;

  // AUTOQ_DEBUG("aut:\n" + this->ToString());
  std::list<std::set<State>> partition;
  std::map<State, std::set<State>*> state_to_class;

  // first process root states
  std::set<State> class_candidate(this->finalStates.begin(), this->finalStates.end());
  for (const auto& symbMapPair : this->transitions) {
    for (const auto& out_ins : symbMapPair.second) { // _ : top down map
      for (const auto& in : out_ins.second) { // _ : childrens
        for (const auto& child : in) {
            if (class_candidate.end() != class_candidate.find(child)) {
                assert(false);
            }
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
    const auto& top_down_map = symbMapPair.second;
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
            std::map<StateVector, StateSet> vector_map;
            for (const auto& out_ins : symbMapPair.second) {
                const auto &out = out_ins.first;
                for (const auto& in : out_ins.second) {
                    vector_map[in].insert(out);
                }
            }
            // const auto& vector_map = symbMapPair.second;
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

template <typename Symbol>
bool AUTOQ::Automata<Symbol>::light_reduce_down_iter()
{
  size_t iterations = 0;
  bool changed = true;
  while (changed) {
    changed = this->light_reduce_down();
    ++iterations;
  }

  return 1 == iterations;
}

template <typename Symbol>
int AUTOQ::Automata<Symbol>::count_states() const {
    int maxState = 0;
    for (const auto &t : transitions) {
        for (const auto &out_ins : t.second) {
            if (maxState < out_ins.first)
                maxState = out_ins.first;
            for (const auto &in : out_ins.second) {
                for (const auto &s : in) {
                    if (maxState < s)
                        maxState = s;
                }
            }
        }
    }
    return maxState + 1;
}

template <typename Symbol>
int AUTOQ::Automata<Symbol>::count_transitions() const {
    int count = 0;
    for (const auto &t : transitions)
        for (const auto &out_ins : t.second) {
            count += out_ins.second.size();
        }
    return count;
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::reduce() {
    auto start = std::chrono::steady_clock::now();
    // AUTOQ_DEBUG("before light_reduce_down: " + Convert::ToString(count_aut_states(*this)));
    // this->sim_reduce(); return;
    this->light_reduce_up_iter();

    Automata old = *this;
    this->light_reduce_down_iter();
    // AUTOQ_DEBUG("after light_reduce_down: " + Convert::ToString(count_aut_states(*this)));

    if (!disableRenumbering)
        compact_aut(*this);
    // assert(check_equal_aut(old, *this));

    auto duration = std::chrono::steady_clock::now() - start;
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename Symbol>
AUTOQ::Automata<Symbol> AUTOQ::Automata<Symbol>::Union(const Automata<Symbol> &o) const {
    if (*this == Automata<Symbol>()) return o;

    Automata<Symbol> result;
    result = *this;
    result.name = "Union";
    if (result.qubitNum != o.qubitNum) {
        throw std::runtime_error(AUTOQ_LOG_PREFIX + "Two automata of different numbers of qubits cannot be unioned together.");
    }
    result.stateNum += o.stateNum;
    // TODO: How to check if the two input automata have different k's?

    for (const auto &t : o.transitions) {
        auto &container = result.transitions[t.first];
        for (const auto &out_ins : t.second) {
            auto out = out_ins.first;
            out += this->stateNum;
            auto &sub_container = container[out];
            for (auto in : out_ins.second) {
                for (unsigned i=0; i<in.size(); i++) {
                    in[i] += this->stateNum;
                }
                sub_container.insert(in);
            }
        }
    }
    for (const auto &s : o.finalStates) {
        result.finalStates.insert(s + this->stateNum);
    }
    result.reduce();
    for (const auto &var : o.vars)
        result.vars.insert(var);
    result.constraints += o.constraints;
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
    return result;
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::print(const std::string &prompt) const {
    std::cout << prompt;
    std::cout << AUTOQ::Serialization::TimbukSerializer::Serialize(*this);
}

template <typename Symbol>
int AUTOQ::Automata<Symbol>::transition_size() {
    int answer = 0;
    for (const auto &t : transitions) {
        for (const auto &in_out : t.second) {
            answer += in_out.second.size();
        }
    }
    return answer;
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
// template <>
// std::vector<std::vector<std::string>> AUTOQ::Automata<Concrete>::print(const std::map<typename AUTOQ::Automata<Concrete>::State, std::set<typename AUTOQ::Automata<Concrete>::Symbol>> &leafSymbolMap, int qubit, typename AUTOQ::Automata<Concrete>::State state) const {
//     if (qubit == static_cast<int>(qubitNum + 1)) {
//         std::vector<std::vector<std::string>> ans;
//         for (const auto &t : leafSymbolMap.at(state)) {
//             std::string result = "(";
//             bool start = false;
//             for (unsigned i=0; i<t.complex.size()-1; i++) {
//                 if (i == 0 && t.complex.at(0) == 0 && t.complex.at(1) == 0 && t.complex.at(2) == 0 && t.complex.at(3) == 0 || t.complex.at(i) != 0) {
//                     if (start) result += " + ";
//                     result += t.complex.at(i).str();
//                     if (i >= 1) result += " * ei2pi(" + std::to_string(i) + "/8)";
//                     start = true;
//                 }
//             }
//             result += ") / sqrt2 ^ " + t.complex.at(4).str();
//             ans.push_back({result});
//         }
//         return ans;
//     }
//     std::vector<std::vector<std::string>> ans;
//     for (const auto &out_ins : transitions.at({qubit})) {
//         if (out_ins.first == state) {
//             for (const auto &in : out_ins.second) {
//                 auto v1 = print(leafSymbolMap, qubit + 1, in.at(0));
//                 auto v2 = print(leafSymbolMap, qubit + 1, in.at(1));
//                 for (const auto &s1 : v1) {
//                     for (const auto &s2 : v2) {
//                         auto v = s1;
//                         v.insert(v.end(), s2.begin(), s2.end());
//                         ans.push_back(v);
//                     }
//                 }
//             }
//         }
//     }
//     return ans;
// }

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
                    std::cout << boost::dynamic_bitset(qubitNum, i) << ":" << s[i] << " | ";
            }
            std::cout << "*:" << (ptr->first) << std::endl;
        }
    }
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Predicate>;
