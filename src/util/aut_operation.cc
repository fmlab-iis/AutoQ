#include <vata/util/aut_description.hh>
#include <vata/util/util.hh>
#include <vata/serialization/timbuk_serializer.hh>

#include "simulation/explicit_lts.hh"

#include <fstream>
#include <numeric>
#include <chrono>

using namespace VATA;
using namespace VATA::Util;

// using State                   = TreeAutomata::State;
// using StateSet                = TreeAutomata::StateSet;
// using StateVector             = TreeAutomata::StateVector;
// using Symbol                  = TreeAutomata::Symbol;
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
  size_t count_aut_states(const VATA::Util::Automata<InitialSymbol>& aut)
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
  typename Util::DiscontBinaryRelation<typename Automata<InitialSymbol>::State> compute_down_sim(const VATA::Util::Automata<InitialSymbol>& aut)
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
      std::__throw_out_of_range("findIndex");
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

    // VATA_DEBUG("Before compact stateNum = " + Convert::ToString(aut.stateNum));
    reindex_aut_states(aut, transl);
    aut.stateNum = stateCnt;
    // VATA_DEBUG("After compact stateNum = " + Convert::ToString(aut.stateNum));
  }

  std::string toString(std::chrono::steady_clock::duration tp)
  {
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
        ss << "TOO_LONG & ";
    else if (m.count() == 0 && s.count() < 10) {
        ss << s.count() << '.' << ms.count() / 100 << "s";
    } else {
        if (m.count() > 0) ss << m.count() << 'm';
        ss << s.count() << 's';// << " & ";
    }
    ss.fill(fill);
    return ss.str();
  }
} // anonymous namespace


template <typename InitialSymbol>
void VATA::Util::Automata<InitialSymbol>::remove_useless(bool only_bottom_up) {
    auto start = std::chrono::steady_clock::now();
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
            const auto &symbol = t.first;
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
                    transitions_remaining.at(symbol).erase(in);
                    changed = true;
                }
            }
            if (transitions_remaining.at(symbol).empty())
                transitions_remaining.erase(symbol);
        }
    } while(changed);
    for (const auto &t : transitions_remaining) {
        const auto &symbol = t.first;
        for (const auto &in_out : t.second)
            transitions.at(symbol).erase(in_out.first);
        if (transitions.at(symbol).empty())
            transitions.erase(symbol);
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
                const auto &symbol = t.first;
                for (const auto &in_out : t.second) {
                    const auto &in = in_out.first;
                    const auto &outs = in_out.second;
                    for (const auto &s : outs) {
                        if (traversed[s]) {
                            for (const auto &v : in)
                                traversed[v] = true;
                            transitions_remaining.at(symbol).at(in).erase(s);
                            changed = true;
                        }
                    }
                    if (transitions_remaining.at(symbol).at(in).empty())
                        transitions_remaining.at(symbol).erase(in);
                }
                if (transitions_remaining.at(symbol).empty())
                    transitions_remaining.erase(symbol);
            }
        } while(changed);
        for (const auto &t : transitions_remaining) {
            const auto &symbol = t.first;
            for (const auto &in_out : t.second) {
                for (const auto &s : in_out.second)
                    transitions.at(symbol).at(in_out.first).erase(s);
                if (transitions.at(symbol).at(in_out.first).empty())
                    transitions.at(symbol).erase(in_out.first);
            }
            if (transitions.at(symbol).empty())
                transitions.erase(symbol);
        }
    }
    /*********************
     * Part 3: Renumbering
     *********************/
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
    auto duration = std::chrono::steady_clock::now() - start;
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename InitialSymbol>
void VATA::Util::Automata<InitialSymbol>::omega_multiplication(int rotation) {
    TransitionMap transitions_new;
    for (const auto &t_old : transitions) {
        const Symbol &symbol = t_old.first;
        if (symbol.is_leaf()) {
            /************************** rotation **************************/
            InitialSymbol sym = symbol.initial_symbol();
            int r = rotation;
            while (r != 0) {
                if (r > 0) {
                    auto temp = sym[3];
                    for (int i=3; i>=1; i--) { // exclude "k"
                        sym[i] = sym[i-1];
                    }
                    sym[0] = -temp;
                    r--;
                } else {
                    auto temp = sym[0];
                    for (int i=0; i<=2; i++) { // exclude "k"
                        sym[i] = sym[i+1];
                    }
                    sym[3] = -temp;
                    r++;
                }
            }
            transitions_new[{sym, symbol.second}] = t_old.second;
        } else {
            assert(symbol.tag().size() <= 1);
            transitions_new.insert(t_old);
        }
    }
    transitions = transitions_new;
    // DO NOT reduce here.
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename InitialSymbol>
void VATA::Util::Automata<InitialSymbol>::divide_by_the_square_root_of_two() {
    std::vector<Symbol> to_be_removed;
    TransitionMap to_be_inserted;
    for (const auto &t : transitions) {
        const Symbol &symbol = t.first;
        if (symbol.is_leaf()) {
            to_be_removed.push_back(symbol);
            InitialSymbol sym = symbol.initial_symbol();
            sym[4]++;
            to_be_inserted[{sym, symbol.tag()}] = t.second;
        }
    }
    for (const auto &t : to_be_removed)
        transitions.erase(t);
    for (const auto &t : to_be_inserted)
        transitions.insert(t);
    // fraction_simplication();
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename InitialSymbol>
void VATA::Util::Automata<InitialSymbol>::branch_restriction(int k, bool positive_has_value) {
    auto start = std::chrono::steady_clock::now();
    State num_of_states = stateNum;
    if (stateNum > std::numeric_limits<State>::max() / 2)
        throw std::overflow_error("");
    stateNum *= 2;

    TransitionMap transitions_copy = transitions;
    for (const auto &t : transitions_copy) {
        const Symbol &symbol = t.first;
        if (symbol.is_internal()) { // x_i + determinized number
            auto &in_outs_dest = transitions.at(symbol);
            for (const auto &in_out : t.second) {
                StateVector in;
                assert(in_out.first.size() == 2);
                for (unsigned i=0; i<in_out.first.size(); i++)
                    in.push_back(in_out.first[i] + num_of_states);
                StateSet out;
                for (const auto &n : in_out.second)
                    out.insert(n + num_of_states);
                in_outs_dest.insert(make_pair(in, out)); // duplicate this internal transition
            }
        } else { // (a,b,c,d,k)
            assert(symbol.is_leaf());
            for (const auto &in_out : t.second) {
                assert(in_out.first.empty());
                for (const auto &n : in_out.second) { // Note we do not change k.
                    auto k = symbol.initial_symbol(4);
                    transitions[{{0,0,0,0, k}, symbol.tag()}][{}].insert(n + num_of_states); // duplicate this leaf transition
                }
            }
        }
    }

    transitions_copy = transitions;
    for (const auto &t : transitions_copy) {
        const Symbol &symbol = t.first;
        if (symbol.is_internal() && symbol.initial_symbol(0) == k) { // x_i + determinized number
            auto &in_outs_dest = transitions.at(symbol);
            for (const auto &in_out : t.second) {
                assert(in_out.first.size() == 2);
                StateVector sv = in_out.first;
                if (in_out.first[0] < num_of_states && in_out.first[1] < num_of_states) {
                    if (positive_has_value) {
                        sv[0] = in_out.first[0] + num_of_states;
                    } else {
                        sv[1] = in_out.first[1] + num_of_states;
                    }
                    in_outs_dest.erase(in_out.first);
                    in_outs_dest.insert(make_pair(sv, in_out.second));
                }
            }
        }
    }
    remove_useless(); // otherwise, will out of memory
    auto end = std::chrono::steady_clock::now();
    branch_rest_time += end - start;
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename InitialSymbol>
void VATA::Util::Automata<InitialSymbol>::semi_determinize() {
    if (isTopdownDeterministic) return;
    TransitionMap transitions_copy = transitions;
    for (const auto &t : transitions_copy) {
        const Symbol &symbol = t.first;
        if (symbol.is_internal()) { // x_i not determinized yet
            assert(!symbol.is_tagged()); // not determinized yet
            transitions.erase(symbol); // modify
            int counter = 0;
            Symbol new_symbol;
            new_symbol.initial_symbol() = symbol.initial_symbol();
            for (const auto &in_out : t.second) {
                new_symbol.tag().push_back(counter++);
                std::map<StateVector, StateSet> value;
                value.insert(in_out);
                transitions.insert(std::make_pair(new_symbol, value)); // modify
                new_symbol.tag().pop_back();
            }
        }
    }
    // DO NOT reduce here.
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename InitialSymbol>
void VATA::Util::Automata<InitialSymbol>::semi_undeterminize() {
    if (isTopdownDeterministic) return;
    TransitionMap transitions_copy = transitions;
    for (const auto &t : transitions_copy) {
        const Symbol &symbol = t.first;
        if (symbol.is_internal()) { // pick all determinized x_i's
            assert(symbol.is_tagged()); // determinized
            transitions.erase(symbol); // modify
            for (const auto &in_out : t.second) {
                for (const auto &v : in_out.second)
                    transitions[symbol.initial_symbol()][in_out.first].insert(v); // modify
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
template <typename InitialSymbol>
VATA::Util::Automata<InitialSymbol> VATA::Util::Automata<InitialSymbol>::binary_operation(const Automata<InitialSymbol> &o, bool add) {
    auto start = std::chrono::steady_clock::now();
    TreeAutomata result;
    result.name = name;
    result.qubitNum = qubitNum;
    result.isTopdownDeterministic = isTopdownDeterministic; // IMPORTANT: Avoid missing copying new fields afterwards.

    std::map<std::pair<State, State>, State> stateOldToNew; // used only if overflow := true;
    bool overflow = (stateNum > std::numeric_limits<State>::max() / o.stateNum);
    if (!overflow)
        result.finalStates.reserve(finalStates.size() * o.finalStates.size()); // TODO: Can we set the initial capacity?
    else
        throw std::overflow_error("");

    for (const auto &fs1 : finalStates)
        for (const auto &fs2 : o.finalStates) {
            construct_product_state_id(fs1, fs2, i);
            result.finalStates.push_back(i);
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
        if (it != transitions.begin() && it->first.initial_symbol(0) != std::prev(it)->first.initial_symbol(0)) { // T1 changes level.
            previous_level_states = previous_level_states2;
            previous_level_states2 = std::vector<bool>(stateNum * o.stateNum);
        }
        // Update next_level_states.
        if (it == transitions.begin() || it->first.initial_symbol(0) != std::prev(it)->first.initial_symbol(0)) { // T1 goes into the new level.
            next_level_states = std::vector<bool>(stateNum * o.stateNum);
            auto it3 = it; // it3 indicates the next level of it.
            while (it3 != transitions.end() && it3->first.is_internal() && it3->first.initial_symbol(0) == it->first.initial_symbol(0))
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
                        for (const auto &s1 : it3->second.begin()->second) { // iterate over all output states of it3
                            for (const auto &s2 : it4->second.begin()->second) { // iterate over all output states of it4
                                construct_product_state_id(s1, s2, i);
                                next_level_states[i] = true; // collect all output state products of the next level
                            }
                        }
                    }
                }
            } else { // The next level of T1 is still internal transitions.
                int current_level = static_cast<int>(it3->first.initial_symbol(0));
                auto it4 = it2; // Initially it2 has the same symbol as it.
                while (it4 != o.transitions.end() && it4->first.is_internal() && it4->first.initial_symbol(0) == current_level)
                    it4++;
                // We hope it4 currently points to T2's first transition of the next level.
                // If it4 points to o.transitions.end(), then the following loop will not be executed.
                for (; it3->first.is_internal() && it3->first.initial_symbol(0) == current_level; it3++) {
                    if (it3->first < it4->first) continue;
                    while (it4 != o.transitions.end() && it3->first > it4->first)
                        it4++;
                    if (it4 == o.transitions.end()) break;
                    if (it3->first < it4->first) continue;
                    assert(it3->first == it4->first);
                    // Ensure T1's and T2's current transitions have the same symbol now.
                    for (auto itt = it3->second.begin(); itt != it3->second.end(); itt++) { // all input-output pairs of it3
                        for (auto itt2 = it4->second.begin(); itt2 != it4->second.end(); itt2++) { // all input-output pairs of it4
                            for (const auto &s1 : itt->second) { // all output states of it3
                                for (const auto &s2 : itt2->second) { // all output states of it4
                                    construct_product_state_id(s1, s2, i);
                                    next_level_states[i] = true; // collect all output state products of the next level
                                }
                            }
                        }
                    }
                }
            }
        }
        std::map<StateVector, StateSet> m;
        for (auto itt = it->second.begin(); itt != it->second.end(); itt++) { // iterate over all input-output pairs of it
            for (auto itt2 = it2->second.begin(); itt2 != it2->second.end(); itt2++) { // iterate over all input-output pairs of it2
                StateVector sv;
                StateSet ss;
                construct_product_state_id(itt->first[0], itt2->first[0], i);
                if (!next_level_states[i]) continue;
                sv.push_back(i); // construct product of T1's and T2's left input states
                construct_product_state_id(itt->first[1], itt2->first[1], j);
                if (!next_level_states[j]) continue;
                sv.push_back(j); // construct product of T1's and T2's right input states
                for (const auto &s1 : itt->second) { // all output states of itt
                    for (const auto &s2 : itt2->second) { // all output states of itt2
                        construct_product_state_id(s1, s2, i);
                        if (previous_level_states[i])
                            ss.insert(i);
                    }
                }
                if (ss.size() > 0) {
                    previous_level_states2[sv[0]] = true;
                    previous_level_states2[sv[1]] = true;
                    m.insert(std::make_pair(sv, ss));
                }
            }
        }
        result.transitions.insert(make_pair(it->first, m));
        assert(m.begin()->first.size() == 2);
    }
    previous_level_states = previous_level_states2;
    // We now advance it2 to T2's first leaf transition.
    while (it2 != o.transitions.end() && !it2->first.is_leaf())
        it2++;
    for (; it != transitions.end(); it++) {
        assert(it->first.is_leaf());
        for (auto it2t = it2; it2t != o.transitions.end(); it2t++) { // it2 as the new begin point.
            assert(it2t->first.is_leaf());
            assert(it->first.initial_symbol(4) == it2t->first.initial_symbol(4)); // Two k's must be the same.
            InitialSymbol symbol;
            for (int i=0; i<4; i++) { // We do not change k here.
                SymbolEntry a = it->first.initial_symbol(i);
                SymbolEntry b = add ? it2t->first.initial_symbol(i) : -it2t->first.initial_symbol(i);
                // if ((a>=0 && b>=0 && a>std::numeric_limits<SymbolEntry>::max()-b)
                //  || (a<0 && b<0 && a<std::numeric_limits<SymbolEntry>::min()-b))
                //     throw std::overflow_error("");
                symbol.push_back(a + b);
            }
            symbol.push_back(it->first.initial_symbol(4)); // remember to push k
            for (const auto &s1 : it->second.begin()->second)
                for (const auto &s2 : it2t->second.begin()->second) {
                    construct_product_state_id(s1, s2, i);
                    if (previous_level_states[i]) {
                        assert(it->first.tag() == it2t->first.tag()); // untagged
                        result.transitions[{symbol, it->first.tag()}][{}].insert(i);
                    }
                }
        }
    }
    if (overflow)
        result.stateNum = stateOldToNew.size();
    else
        result.stateNum = stateNum * o.stateNum;
    result.remove_useless(true); // otherwise, will out of memory
    auto end = std::chrono::steady_clock::now();
    binop_time += end - start;
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
    return result;
}

template <typename InitialSymbol>
VATA::Util::Automata<InitialSymbol> VATA::Util::Automata<InitialSymbol>::Union(const Automata<InitialSymbol> &o) {
    Automata<InitialSymbol> result;
    result = *this;
    result.name = "Union";
    assert(result.qubitNum == o.qubitNum);
    result.stateNum += o.stateNum;

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
VATA::Util::Automata<InitialSymbol> VATA::Util::Automata<InitialSymbol>::uniform(int n) {
    Automata<InitialSymbol> aut;
    aut.name = "Uniform";
    aut.qubitNum = n;
    int pow_of_two = 1;
    State state_counter = 0;
    for (int level=1; level<=n; level++) {
        for (int i=0; i<pow_of_two; i++) {
            if (level < n)
                aut.transitions[{level}][{state_counter*2+1, state_counter*2+2}] = {state_counter};
            else
                aut.transitions[{level}][{pow_of_two*2-1, pow_of_two*2-1}].insert(state_counter);
            state_counter++;
        }
        pow_of_two *= 2;
    }
    aut.transitions[{1,0,0,0,n}][{}] = {pow_of_two-1};
    aut.finalStates.push_back(0);
    aut.stateNum = pow_of_two;

    // aut.minimize();
    // aut.isTopdownDeterministic = true;
    return aut;
}

template <typename InitialSymbol>
VATA::Util::Automata<InitialSymbol> VATA::Util::Automata<InitialSymbol>::basis(int n) {
    Automata<InitialSymbol> aut;
    aut.name = "Classical";
    aut.qubitNum = n;

    for (int level=1; level<=n; level++) {
        if (level >= 2)
            aut.transitions[{level}][{2*level - 1, 2*level - 1}] = {2*level - 3};
        aut.transitions[{level}][{2*level - 1, 2*level}] = {2*level - 2};
        aut.transitions[{level}][{2*level, 2*level - 1}] = {2*level - 2};
    }
    aut.transitions[{1,0,0,0,0}][{}] = {2*n};
    aut.transitions[{0,0,0,0,0}][{}] = {2*n - 1};
    aut.finalStates.push_back(0);
    aut.stateNum = 2*n + 1;

    // aut.minimize();
    return aut;
}

template <typename InitialSymbol>
VATA::Util::Automata<InitialSymbol> VATA::Util::Automata<InitialSymbol>::random(int n) {
    Automata<InitialSymbol> aut;
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
        aut.transitions[{rand()%5, rand()%5, rand()%5, rand()%5, 0}][{}].insert(i);
    }
    aut.finalStates.push_back(0);
    aut.stateNum = state_counter*2 + 1;

    // aut.minimize();
    // aut.isTopdownDeterministic = true;
    return aut;
}

template <typename InitialSymbol>
VATA::Util::Automata<InitialSymbol> VATA::Util::Automata<InitialSymbol>::zero(int n) {
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
    Automata<InitialSymbol> aut;
    aut.name = "Zero";
    aut.qubitNum = n;
    aut.finalStates.push_back(0);
    aut.transitions[{1}][{2,1}] = {0};
    for (int level=2; level<=n; level++) {
        aut.transitions[{level}][{level*2-1, level*2-1}] = {level*2-3};
        aut.transitions[{level}][{level*2, level*2-1}] = {level*2-2};
    }
    aut.transitions[{0,0,0,0,0}][{}].insert(n*2-1);
    aut.transitions[{1,0,0,0,0}][{}].insert(n*2);
    aut.stateNum = n*2 + 1;

    // aut.minimize();
    // aut.isTopdownDeterministic = true;
    return aut;
}

template <typename InitialSymbol>
VATA::Util::Automata<InitialSymbol> VATA::Util::Automata<InitialSymbol>::basis_zero_one_zero(int n) {
    Automata<InitialSymbol> aut;
    assert(n >= 2);
    aut.name = "Classical_Zero_One_Zero";
    aut.qubitNum = n + (n+1) + (n>=3) * (n-1);

    for (int level=1; level<=n; level++) {
        if (level >= 2)
            aut.transitions[{level}][{2*level - 1, 2*level - 1}] = {2*level - 3};
        aut.transitions[{level}][{2*level - 1, 2*level}] = {2*level - 2};
        aut.transitions[{level}][{2*level, 2*level - 1}] = {2*level - 2};
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
        aut.transitions[{1,0,0,0,0}][{}] = {6*n};
        aut.transitions[{0,0,0,0,0}][{}] = {6*n - 1};
        aut.stateNum = 6*n + 1;
    } else {
        assert(n == 2);
        aut.transitions[{1,0,0,0,0}][{}] = {4*n + 2};
        aut.transitions[{0,0,0,0,0}][{}] = {4*n + 1};
        aut.stateNum = 4*n + 3;
    }
	aut.finalStates.push_back(0);
    return aut;
}

template <typename InitialSymbol>
VATA::Util::Automata<InitialSymbol> VATA::Util::Automata<InitialSymbol>::zero_zero_one_zero(int n) {
    Automata<InitialSymbol> aut;
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
        aut.transitions[{1,0,0,0,0}][{}] = {6*n};
        aut.transitions[{0,0,0,0,0}][{}] = {6*n - 1};
        aut.stateNum = 6*n + 1;
    } else {
        assert(n == 2);
        aut.transitions[{1,0,0,0,0}][{}] = {4*n + 2};
        aut.transitions[{0,0,0,0,0}][{}] = {4*n + 1};
        aut.stateNum = 4*n + 3;
    }
	aut.finalStates.push_back(0);
    // aut.isTopdownDeterministic = true;
    return aut;
}

template <typename InitialSymbol>
VATA::Util::Automata<InitialSymbol> VATA::Util::Automata<InitialSymbol>::zero_one_zero(int n) {
    Automata<InitialSymbol> aut;
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
        aut.transitions[{1,0,0,0,0}][{}] = {4*n};
        aut.transitions[{0,0,0,0,0}][{}] = {4*n - 1};
        aut.stateNum = 4*n + 1;
    } else {
        assert(n == 2);
        aut.transitions[{1,0,0,0,0}][{}] = {2*n + 2};
        aut.transitions[{0,0,0,0,0}][{}] = {2*n + 1};
        aut.stateNum = 2*n + 3;
    }
	aut.finalStates.push_back(0);
    // aut.isTopdownDeterministic = true;
    return aut;
}

template <typename InitialSymbol>
void VATA::Util::Automata<InitialSymbol>::swap_forward(const int k) {
    if (isTopdownDeterministic) return;
    for (int next_k=k+1; next_k<=qubitNum; next_k++) {
        std::map<State, std::vector<std::pair<Symbol, StateVector>>> svsv;
        for (const auto &t : transitions) {
            const auto &symbol = t.first;
            const auto &in_outs = t.second;
            if (symbol.is_internal() && symbol.initial_symbol(0) == next_k) {
                assert(symbol.tag().size() <= 1);
                for (const auto &in_out : in_outs) {
                    for (const auto &s : in_out.second)
                        svsv[s].push_back(make_pair(symbol, in_out.first));
                }
            }
        }
        std::vector<Symbol> to_be_removed2;
        TransitionMap to_be_removed, to_be_inserted;
        for (const auto &t : transitions) {
            const Symbol &symbol = t.first;
            if (symbol.is_internal() && symbol.initial_symbol(0) == k) {
                for (const auto &in_out : t.second) {
                    assert(in_out.first.size() == 2);
                    for (const auto &ssv1 : svsv[in_out.first[0]]) {
                        for (const auto &ssv2 : svsv[in_out.first[1]]) {
                            to_be_removed[ssv1.first][ssv1.second].insert(in_out.first[0]);
                            to_be_removed[ssv2.first][ssv2.second].insert(in_out.first[1]);
                            if (to_be_inserted[symbol][{ssv1.second[0], ssv2.second[0]}].empty()) {
                                if (transitions[symbol][{ssv1.second[0], ssv2.second[0]}].empty())
                                    to_be_inserted[symbol][{ssv1.second[0], ssv2.second[0]}].insert(stateNum++);
                                else
                                    to_be_inserted[symbol][{ssv1.second[0], ssv2.second[0]}].insert(*(transitions[symbol][{ssv1.second[0], ssv2.second[0]}].begin()));
                            }
                            if (to_be_inserted[symbol][{ssv1.second[1], ssv2.second[1]}].empty()) {
                                if (transitions[symbol][{ssv1.second[1], ssv2.second[1]}].empty())
                                    to_be_inserted[symbol][{ssv1.second[1], ssv2.second[1]}].insert(stateNum++);
                                else
                                    to_be_inserted[symbol][{ssv1.second[1], ssv2.second[1]}].insert(*(transitions[symbol][{ssv1.second[1], ssv2.second[1]}].begin()));
                            }
                            for (const auto &s : in_out.second)
                                to_be_inserted[{{next_k}, {ssv1.first.tag(0), ssv2.first.tag(0)}}][{*(to_be_inserted[symbol][{ssv1.second[0], ssv2.second[0]}].begin()), *(to_be_inserted[symbol][{ssv1.second[1], ssv2.second[1]}].begin())}].insert(s);
                        }
                    }
                }
                to_be_removed2.push_back(symbol);
            }
        }
        for (const auto &v : to_be_removed2)
            transitions.erase(v);
        for (const auto &t : to_be_removed) {
            const Symbol &symbol = t.first;
            for (const auto &in_out : t.second) {
                for (const auto &s : in_out.second)
                    transitions[symbol][in_out.first].erase(s);
                if (transitions[symbol][in_out.first].empty())
                    transitions[symbol].erase(in_out.first);
                if (transitions[symbol].empty())
                    transitions.erase(symbol);
            }
        }
        for (const auto &t : to_be_inserted) {
            const Symbol &symbol = t.first;
            for (const auto &in_out : t.second) {
                for (const auto &s : in_out.second) {
                    transitions[symbol][in_out.first].insert(s);
                }
            }
        }
        // DO NOT reduce here.
    }
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename InitialSymbol>
void VATA::Util::Automata<InitialSymbol>::swap_backward(const int k) {
    if (isTopdownDeterministic) return;
    for (int next_k=qubitNum; next_k>k; next_k--) {
      std::map<State, std::vector<std::pair<Symbol, StateVector>>> svsv;
        for (const auto &t : transitions) {
            const auto &symbol = t.first;
            const auto &in_outs = t.second;
            if (symbol.is_internal() && symbol.initial_symbol(0) == k) {
                assert(symbol.tag().size() == 1);
                for (const auto &in_out : in_outs) {
                    for (const auto &s : in_out.second)
                        svsv[s].push_back(make_pair(symbol, in_out.first));
                }
            }
        }
        std::vector<Symbol> to_be_removed2;
        TransitionMap to_be_removed, to_be_inserted;
        for (const auto &t : transitions) {
            const Symbol &symbol = t.first;
            if (symbol.is_internal() && symbol.initial_symbol(0) == next_k) {
                assert(symbol.tag().size() == 2);
                for (const auto &in_out : t.second) {
                    assert(in_out.first.size() == 2);
                    for (const auto &ssv1 : svsv[in_out.first[0]]) {
                        for (const auto &ssv2 : svsv[in_out.first[1]]) {
                            if (ssv1.first == ssv2.first) {
                                to_be_removed[ssv1.first][ssv1.second].insert(in_out.first[0]);
                                to_be_removed[ssv2.first][ssv2.second].insert(in_out.first[1]);
                                Symbol t1 = {symbol.initial_symbol(), {symbol.tag(0)}};
                                if (to_be_inserted[t1][{ssv1.second[0], ssv2.second[0]}].empty()) {
                                    if (transitions[t1][{ssv1.second[0], ssv2.second[0]}].empty())
                                        to_be_inserted[t1][{ssv1.second[0], ssv2.second[0]}].insert(stateNum++);
                                    else
                                        to_be_inserted[t1][{ssv1.second[0], ssv2.second[0]}].insert(*(transitions[t1][{ssv1.second[0], ssv2.second[0]}].begin()));
                                }
                                Symbol t2 = {symbol.initial_symbol(), {symbol.tag(1)}};
                                if (to_be_inserted[t2][{ssv1.second[1], ssv2.second[1]}].empty()) {
                                    if (transitions[t2][{ssv1.second[1], ssv2.second[1]}].empty())
                                        to_be_inserted[t2][{ssv1.second[1], ssv2.second[1]}].insert(stateNum++);
                                    else
                                        to_be_inserted[t2][{ssv1.second[1], ssv2.second[1]}].insert(*(transitions[t2][{ssv1.second[1], ssv2.second[1]}].begin()));
                                }
                                assert(k == ssv1.first.initial_symbol(0));
                                for (const auto &s : in_out.second)
                                    to_be_inserted[ssv1.first][{*(to_be_inserted[t1][{ssv1.second[0], ssv2.second[0]}].begin()), *(to_be_inserted[t2][{ssv1.second[1], ssv2.second[1]}].begin())}].insert(s);
                            }
                        }
                    }
                }
                to_be_removed2.push_back(symbol);
            }
        }
        for (const auto &v : to_be_removed2)
            transitions.erase(v);
        for (const auto &t : to_be_removed) {
            const Symbol &symbol = t.first;
            for (const auto &in_out : t.second) {
                for (const auto &s : in_out.second)
                    transitions[symbol][in_out.first].erase(s);
                if (transitions[symbol][in_out.first].empty())
                    transitions[symbol].erase(in_out.first);
                if (transitions[symbol].empty())
                    transitions.erase(symbol);
            }
        }
        for (const auto &t : to_be_inserted) {
            const Symbol &symbol = t.first;
            for (const auto &in_out : t.second) {
                for (const auto &s : in_out.second) {
                    transitions[symbol][in_out.first].insert(s);
                }
            }
        }
        // DO NOT reduce here.
    }
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename InitialSymbol>
void VATA::Util::Automata<InitialSymbol>::value_restriction(int k, bool branch) {
    auto start = std::chrono::steady_clock::now();
    swap_forward(k);
    TransitionMap to_be_inserted;
    std::vector<Symbol> to_be_removed;
    for (const auto &t : transitions) {
        const Symbol &symbol = t.first;
        if (symbol.is_internal() && symbol.initial_symbol(0) == k) {
            to_be_removed.push_back(symbol);
            for (const auto &in_out : t.second) {
                assert(in_out.first.size() == 2);
                for (const auto &s : in_out.second) {
                    if (branch)
                        to_be_inserted[symbol][{in_out.first[1], in_out.first[1]}].insert(s);
                    else
                        to_be_inserted[symbol][{in_out.first[0], in_out.first[0]}].insert(s);
                }
            }
        }
    }
    for (const auto &t : to_be_removed) {
        transitions.erase(t);
    }
    for (const auto &t : to_be_inserted) {
        transitions[t.first] = t.second;
    }
    swap_backward(k);
    this->reduce();
    auto end = std::chrono::steady_clock::now();
    value_rest_time += end - start;
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename InitialSymbol>
void VATA::Util::Automata<InitialSymbol>::fraction_simplication() {
    std::vector<Symbol> to_be_removed;
    TransitionMap to_be_inserted;
    for (const auto &t : transitions) {
        Symbol symbol = t.first;
        if (symbol.is_leaf()) {
            InitialSymbol &sym = symbol.initial_symbol();
            if (sym[0]==0 && sym[1]==0 && sym[2]==0 && sym[3]==0) sym[4] = 0;
            else {
                while ((sym[0]&1)==0 && (sym[1]&1)==0 && (sym[2]&1)==0 && (sym[3]&1)==0 && sym[4]>=2) { // Notice the parentheses enclosing sym[i]&1 are very important! HAHA
                    for (int i=0; i<4; i++) sym[i] /= 2;
                    sym[4] -= 2;
                }
            }
            if (t.first != symbol) {
                to_be_removed.push_back(t.first);
                for (const auto &in_out : t.second) {
                    for (const auto &s : in_out.second) {
                        to_be_inserted[symbol][in_out.first].insert(s);
                    }
                }
            }
        }
    }
    for (const auto &t : to_be_removed) transitions.erase(t);
    for (const auto &t : to_be_inserted) transitions.insert(t);
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

/**************** Equivalence Checking ****************/
// namespace
// { // anonymous namespace
  std::string gpath_to_VATA = "";

  /** returns the path to VATA executable */
  const std::string& get_vata_path()
  {
    // is it cached?
    if (!gpath_to_VATA.empty()) return gpath_to_VATA;

    // not cached, get it from ENV
    const char* path = std::getenv("VATA_PATH");
    if (nullptr == path) {
      throw std::runtime_error("Cannot find environment variable VATA_PATH");
    }

    gpath_to_VATA = path;
    return gpath_to_VATA;
  }


  /** checks inclusion of two TAs */
  template <typename InitialSymbol>
  bool VATA::Util::Automata<InitialSymbol>::check_inclusion(const std::string& lhsPath, const std::string& rhsPath)
  {
    std::string aux;
    VATA::Util::ShellCmd(get_vata_path() + " incl " + lhsPath + " " + rhsPath, aux);
    return (aux == "1\n");
  }

  /** checks language equivalence of two TAs */
  template <typename InitialSymbol>
  bool VATA::Util::Automata<InitialSymbol>::check_equal(const std::string& lhsPath, const std::string& rhsPath)
  {
    return check_inclusion(lhsPath, rhsPath) && check_inclusion(rhsPath, lhsPath);
  }

  template <typename InitialSymbol>
  bool VATA::Util::Automata<InitialSymbol>::check_equal_aut(
      VATA::Util::Automata<InitialSymbol> lhs,
      VATA::Util::Automata<InitialSymbol> rhs)
  {
	std::ofstream fileLhs("/tmp/automata1.txt");
    lhs.fraction_simplication();
	fileLhs << VATA::Serialization::TimbukSerializer::Serialize(lhs);
	fileLhs.close();

	std::ofstream fileRhs("/tmp/automata2.txt");
    rhs.fraction_simplication();
	fileRhs << VATA::Serialization::TimbukSerializer::Serialize(rhs);
	fileRhs.close();

	return check_equal("/tmp/automata1.txt", "/tmp/automata2.txt");
  }
// } // anonymous namespace
/******************************************************/

template <typename InitialSymbol>
void VATA::Util::Automata<InitialSymbol>::sim_reduce()
{
  using State = typename Automata<InitialSymbol>::State;
  using DiscontBinaryRelOnStates = typename Util::DiscontBinaryRelation<State>;
  using StateToStateMap = typename std::unordered_map<State, State>;

  DiscontBinaryRelOnStates sim = compute_down_sim(*this);

  // TODO: this is probably not optimal, we could probably get the mapping of
  // states for collapsing in a faster way
  sim.RestrictToSymmetric();       // sim is now an equivalence relation

  StateToStateMap collapseMap;
  sim.GetQuotientProjection(collapseMap);

  // Automata old = *this;
  reindex_aut_states(*this, collapseMap);

  // if (!check_equal_aut(*this, old)) {
  //   VATA_DEBUG("wrong simulation result!");
  //   VATA_DEBUG("old: " + old.ToString());
  //   VATA_DEBUG("new: " + this->ToString());
  //   VATA_DEBUG("simulation: " + sim.ToString());
  // }
}

template <typename InitialSymbol>
bool VATA::Util::Automata<InitialSymbol>::light_reduce_up()
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

  // VATA_DEBUG("index: " + Convert::ToString(index));
  if (changed) {
    // Automata old = *this;
    reindex_aut_states(*this, index);
    // assert(check_equal_aut(old, *this));
  }

  return changed;
}

template <typename InitialSymbol>
bool VATA::Util::Automata<InitialSymbol>::light_reduce_up_iter()
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
bool VATA::Util::Automata<InitialSymbol>::light_reduce_down()
{
  using State = typename Automata<InitialSymbol>::State;
  using StateToStateMap = typename std::unordered_map<State, State>;
  using StateToStateTranslWeak = typename Util::TranslatorWeak<StateToStateMap>;

  // VATA_DEBUG("aut:\n" + this->ToString());
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
    // VATA_DEBUG("top down map: " + Convert::ToString(top_down_map));

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
      // VATA_DEBUG("left child map: " + Convert::ToString(left_child_map));
      // VATA_DEBUG("right child map: " + Convert::ToString(right_child_map));

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
          // VATA_DEBUG("index: " + Convert::ToString(index));
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
                //   VATA_DEBUG("Sanity check in downward light reduction failed, not reducing!");
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
bool VATA::Util::Automata<InitialSymbol>::light_reduce_down_iter()
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
void VATA::Util::Automata<InitialSymbol>::reduce()
{
  auto start = std::chrono::steady_clock::now();
  // VATA_DEBUG("before light_reduce_down: " + Convert::ToString(count_aut_states(*this)));
  // this->sim_reduce();
  this->light_reduce_up_iter();


  Automata old = *this;
  this->light_reduce_down_iter();
  // VATA_DEBUG("after light_reduce_down: " + Convert::ToString(count_aut_states(*this)));

  compact_aut(*this);
  assert(check_equal_aut(old, *this));

  auto duration = std::chrono::steady_clock::now() - start;
  if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}

template <typename InitialSymbol>
void VATA::Util::Automata<InitialSymbol>::print() {
    std::string result;

  result += "Ops ";
  for (auto itSymb = transitions.cbegin();
    itSymb != transitions.cend(); ++itSymb)
  {
    result += VATA::Util::Convert::ToString(itSymb->first) + ":" +
      VATA::Util::Convert::ToString(itSymb->second.begin()->first.size()) + " ";
  }

  result += "\n";
  result += "Automaton " + (name.empty()? "anonymous" : name);

  result += "\n";
  result += "States ";
    for (State i=0; i<stateNum; i++) {
        result += std::to_string(i) + " ";
        // result += stateNum.TranslateBwd(i) + " ";
    }
  // for_each(states.cbegin(), states.cend(),
  //  [&result](const std::string& sStr){ result += sStr + " ";});

  result += "\n";
  result += "Final States ";
    for (State i : finalStates) {
        result += std::to_string(i) + " ";
        // result += stateNum.TranslateBwd(i) + " ";
    }
  // for_each(finalStates.cbegin(), finalStates.cend(),
  //  [&result](const std::string& fsStr){ result += fsStr + " ";});

  result += "\n";
  result += "Transitions\n";

    for (const auto &t : transitions) {
        for (const auto &t2 : t.second) {
            for (const auto &finalSet : t2.second) {
                result += Convert::ToString(t.first);
                if (!(t2.first.empty())) {
                    result += "(";
                    result += std::to_string(t2.first[0]); //stateNum.TranslateBwd(t2.first[0]);
                    for (size_t i = 1; i < t2.first.size(); ++i) {
                        result += ", ";
                        result += std::to_string(t2.first[i]); //stateNum.TranslateBwd(t2.first[i]);
                    }
                    result += ")";
                }
                result += " -> ";
                result += std::to_string(finalSet); //stateNum.TranslateBwd(finalSet);
                result += "\n";
            }
        }
    }
    std::cout << result; // << "\n";
}

template <typename InitialSymbol>
int VATA::Util::Automata<InitialSymbol>::transition_size() {
    int answer = 0;
    for (const auto &t : transitions) {
        for (const auto &in_out : t.second) {
            answer += in_out.second.size();
        }
    }
    return answer;
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct VATA::Util::Automata<VATA::Util::Concrete>;