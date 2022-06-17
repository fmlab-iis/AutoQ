#include <vata/util/aut_description.hh>
#include <vata/util/util.hh>
#include <vata/serialization/timbuk_serializer.hh>

#include "simulation/explicit_lts.hh"

#include <fstream>
#include <numeric>

using namespace VATA;
using namespace VATA::Util;

using State                   = TreeAutomata::State;
using StateSet                = TreeAutomata::StateSet;
using StateVector             = TreeAutomata::StateVector;
using Symbol                  = TreeAutomata::Symbol;
using TransitionMap           = TreeAutomata::TransitionMap;

using DiscontBinaryRelOnStates= DiscontBinaryRelation<State>;
using StateToIndexMap         = std::unordered_map<State, size_t>;
using StateToIndexTranslWeak  = Util::TranslatorWeak<StateToIndexMap>;

template <class T>
int findIndex(const std::vector<T> &arr, T item) {
    for (int i = 0; i < static_cast<int>(arr.size()); ++i) {
        if (arr[i] == item)
            return i;
    }
    std::__throw_out_of_range("findIndex");
}

bool VATA::Util::TreeAutomata::is_same_partition(const std::vector<int> &state_to_partition_id, State a, State b) {
    assert (state_to_partition_id[a] == state_to_partition_id[b]);
    for (const auto &f : transitions) { // for all functions
        int arity = f.second.begin()->first.size();
        if (arity < 1) continue; // no test if arity == 0
        StateVector sv(arity, 0); // declare the input states
        bool overflow;
        do {
            for (int i=0; i<arity; i++) {
                sv[i] = a;
                int resultA, resultB;
                try {
                    assert(transitions.at(f.first).at(sv).size() == 1);
                    resultA = state_to_partition_id[*(transitions.at(f.first).at(sv).begin())];
                } catch (...) { // must use .at in order to trigger exceptions if out of bound
                    resultA = -1;
                }
                sv[i] = b;
                try {
                    assert(transitions.at(f.first).at(sv).size() == 1);
                    resultB = state_to_partition_id[*(transitions.at(f.first).at(sv).begin())];
                } catch (...) { // must use .at in order to trigger exceptions if out of bound
                    resultB = -1;
                }
                if (resultA != resultB) return false;
                if (i+1 < arity)
                    std::swap(sv[i], sv[i+1]);
            }
            for (int i=0; i<arity-1; i++) {
              std::swap(sv[i], sv[i+1]);
            }

            overflow = (arity == 1);
            if (!overflow) { // arity > 1
                sv[1]++;
                for (int i=1; i<arity; i++) {
                    if (sv[i] == stateNum) {
                        if (i == arity - 1) {
                            overflow = true;
                            break;
                        } else {
                            sv[i] = 0;
                            sv[i+1]++;
                        }
                    } else break;
                }
            }
        } while (!overflow);
    }
    return true;
}

void VATA::Util::TreeAutomata::remove_useless() {
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
                    // assert(outs.size() == 1);
                    for (const auto &s : outs)
                        traversed[s/**(outs.begin())*/] = true;
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
                // assert(outs.size() == 1);
                for (const auto &s : outs) {
                    if (traversed[s /**(outs.begin())*/]) {
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

    /*********************
     * Part 3: Renumbering
     *********************/
    TransitionMap transitions_new;
    std::map<int, int> stateOldToNew;
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
            // assert(outs.size() == 1);
            for (const auto &s : outs) {
                State newState = stateOldToNew.size();
                auto itBoolPair = stateOldToNew.insert({s, newState});
                if (!itBoolPair.second) { // if insertion didn't happened
                    const auto& it = itBoolPair.first;
                    newState = it->second;
                }
                transitions_new[t.first][sv].insert(newState);
                // transitions_new[t.first].insert(make_pair(sv, StateSet({dest})));
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
        // it could severely degrade the performance (with or without sim_reduce()).
    }
    finalStates = finalStates_new;
    stateNum = stateOldToNew.size();
}

void VATA::Util::TreeAutomata::integer_multiplication(int m) {
    TransitionMap transitions_new;
    for (const auto &t_old : transitions) {
        if (t_old.first.size() == 5) {
            Symbol temp;
            for (unsigned i=0; i<t_old.first.size()-1; i++) { // exclude "k"
                temp.push_back(t_old.first[i] * m);
            }
            temp.push_back(t_old.first[t_old.first.size()-1]);
            try {
                auto &in_out = transitions_new.at(temp);
                for (const auto &kv : t_old.second) {
                    try {
                        StateSet &ss = in_out.at(kv.first);
                        StateSet dest;
                        set_union(ss.begin(), ss.end(), kv.second.begin(), kv.second.end(), inserter(dest, dest.begin()));
                        ss = dest;
                    } catch (...) {
                        in_out[kv.first] = kv.second;
                    }
                }
            } catch (...) {
                transitions_new[temp] = t_old.second;
            }
        } else {
            assert(t_old.first.size() <= 2);
            transitions_new.insert(t_old);
        }
    }
    transitions = transitions_new;
    // DO NOT reduce here.
}

void VATA::Util::TreeAutomata::omega_multiplication() {
    TransitionMap transitions_new;
    for (const auto &t_old : transitions) {
        if (t_old.first.size() == 5) {
            Symbol temp;
            temp.push_back(-t_old.first[3]);
            for (unsigned i=0; i<t_old.first.size()-2; i++) { // exclude "k"
                temp.push_back(t_old.first[i]);
            }
            temp.push_back(t_old.first[t_old.first.size()-1]);
            auto it = transitions_new.find(temp);   // has the symbol been used?
            if (transitions_new.end() != it) { // found it!
                auto &in_out = it->second;
                for (const auto &kv : t_old.second) { // go over all states in the set of parents
                    auto jt = in_out.find(kv.first);    // try to find the tuple
                    if (in_out.end() != jt) { // found it!
                        StateSet &ss = jt->second;
                        StateSet dest;
                        set_union(ss.begin(), ss.end(), kv.second.begin(), kv.second.end(), inserter(dest, dest.begin()));
                        ss = dest;
                    } else {
                        in_out[kv.first] = kv.second;
                    }
                }
            } else { // didn't find it
                transitions_new[temp] = t_old.second;
            }
        } else {
            assert(t_old.first.size() <= 2);
            transitions_new.insert(t_old);
        }
    }
    transitions = transitions_new;
    // DO NOT reduce here.
}

void VATA::Util::TreeAutomata::divide_by_the_square_root_of_two() {
    std::vector<StateVector> to_be_removed;
    TransitionMap to_be_inserted;
    for (const auto &t : transitions) {
        if (t.first.size() == 5) {
            to_be_removed.push_back(t.first);
            StateVector sv = t.first;
            sv[4]++;
            to_be_inserted[sv] = t.second;
        }
    }
    for (const auto &t : to_be_removed)
        transitions.erase(t);
    for (const auto &t : to_be_inserted)
        transitions.insert(t);
    // fraction_simplication();
}

void VATA::Util::TreeAutomata::branch_restriction(int k, bool positive_has_value) {
    int num_of_states = stateNum;
    stateNum *= 2;

    TransitionMap transitions_copy = transitions;
    for (const auto &t : transitions_copy) {
        if (t.first.size() <= 2) { // x_i + determinized number
            auto &in_outs_dest = transitions.at(t.first);
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
            assert(t.first.size() == 5);
            for (const auto &in_out : t.second) {
                assert(in_out.first.empty());
                for (const auto &n : in_out.second) { // Note we do not change k.
                    transitions[{0,0,0,0, t.first[4]}][{}].insert(n + num_of_states); // duplicate this leaf transition
                }
            }
        }
    }

    transitions_copy = transitions;
    for (const auto &t : transitions_copy) {
        if (t.first.size() <= 2 && t.first[0] == k) { // x_i + determinized number
            auto &in_outs_dest = transitions.at(t.first);
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
}

void VATA::Util::TreeAutomata::semi_determinize() {
    TransitionMap transitions_copy = transitions;
    for (const auto &t : transitions_copy) {
        if (t.first.size() == 1) { // x_i not determinized yet
            transitions.erase(t.first); // modify
            int counter = 0;
            StateVector sv;
            sv.push_back(t.first[0]);
            for (const auto &in_out : t.second) {
                sv.push_back(counter++);
                std::map<StateVector, StateSet> value;
                value.insert(in_out);
                transitions.insert(std::make_pair(sv, value)); // modify
                sv.pop_back();
            }
        }
    }
    // DO NOT reduce here.
}

void VATA::Util::TreeAutomata::semi_undeterminize() {
    TransitionMap transitions_copy = transitions;
    for (const auto &t : transitions_copy) {
        if (t.first.size() == 2) { // pick all determinized x_i's
            transitions.erase(t.first); // modify
            for (const auto &in_out : t.second) {
                for (const auto &v : in_out.second)
                    transitions[{t.first[0]}][in_out.first].insert(v); // modify
            }
        }
    }
    sim_reduce();
}

VATA::Util::TreeAutomata VATA::Util::TreeAutomata::binary_operation(const TreeAutomata &o, bool add) {
    TreeAutomata result;
    result.name = name;
    result.qubitNum = qubitNum;
    result.stateNum = stateNum * o.stateNum;

    for (const auto &fs1 : finalStates)
        for (const auto &fs2 : o.finalStates) {
            result.finalStates.insert(fs1 * o.stateNum + fs2);
        }

    // We assume here transitions are ordered by symbols.
    // x_i are placed in the beginning, and leaves are placed in the end.
    // This traversal method is due to efficiency.
    auto it = transitions.begin();
    for (; it != transitions.end(); it++) {
        if (it->first.size() == 5) break;
        auto it2 = o.transitions.begin();
        // assert(it->first == it2->first); // both sources contain the same x_i^k
        while (it2 != o.transitions.end() && it->first != it2->first)
            it2++;
        if (it2 == o.transitions.end()) continue;
        // assert(it->second.size() == 1); // both sources contain the unique I/O
        // assert(it2->second.size() == 1); // i.e., map<StateVector, StateSet> is singleton.
        std::map<StateVector, StateSet> m;
        for (auto itt = it->second.begin(); itt != it->second.end(); itt++)
            for (auto itt2 = it2->second.begin(); itt2 != it2->second.end(); itt2++) {
                StateVector sv;
                StateSet ss;
                sv.push_back(itt->first[0] * o.stateNum + itt2->first[0]);
                sv.push_back(itt->first[1] * o.stateNum + itt2->first[1]);
                for (const auto &s1 : itt->second) {
                    for (const auto &s2 : itt2->second) {
                        ss.insert(s1 * o.stateNum + s2);
                    }
                }
                m.insert(make_pair(sv, ss));
            }
        result.transitions.insert(make_pair(it->first, m));
        assert(m.begin()->first.size() == 2);
    }
    auto it2 = o.transitions.begin();
    while (it2 != o.transitions.end() && it2->first.size() != 5)
        it2++;
    for (; it != transitions.end(); it++) {
        assert(it->first.size() == 5);
        for (auto it2t = it2; it2t != o.transitions.end(); it2t++) { // it2 as the new begin point.
            assert(it2t->first.size() == 5);
            StateVector in;
            if (it->first[4] <= it2t->first[4]) {
                int k_diff = it2t->first[4] - it->first[4];
                assert(k_diff % 2 == 0);
                int pow = 1;
                while (k_diff > 0) {
                    pow *= 2;
                    k_diff -= 2;
                }
                for (int i=0; i<4; i++) {
                    if (add)
                        in.push_back(it->first[i] * pow + it2t->first[i]);
                    else
                        in.push_back(it->first[i] * pow - it2t->first[i]);
                }
                in.push_back(it2t->first[4]); // remember to push k
            } else {
                int k_diff = it->first[4] - it2t->first[4];
                assert(k_diff % 2 == 0);
                int pow = 1;
                while (k_diff > 0) {
                    pow *= 2;
                    k_diff -= 2;
                }
                for (int i=0; i<4; i++) {
                    if (add)
                        in.push_back(it->first[i] + it2t->first[i] * pow);
                    else
                        in.push_back(it->first[i] - it2t->first[i] * pow);
                }
                in.push_back(it->first[4]); // remember to push k
            }
            // assert(it->first[4] == it2t->first[4]); // Two k's must be the same.
            // StateVector in;
            // for (int i=0; i<4; i++) { // We do not change k here.
            //     if (add)
            //         in.push_back(it->first[i] + it2t->first[i]);
            //     else
            //         in.push_back(it->first[i] - it2t->first[i]);
            // }
            // in.push_back(it->first[4]); // remember to push k
            for (const auto &s1 : it->second.begin()->second)
                for (const auto &s2 : it2t->second.begin()->second)
                    result.transitions[in][{}].insert(s1 * o.stateNum + s2);
                    // result.transitions[in][{}].insert((*(it->second.begin()->second.begin())) * o.stateNum + (*(it2t->second.begin()->second.begin())));
        }
    }
    result.remove_useless(); // otherwise, will out of memory
    return result;
}

VATA::Util::TreeAutomata VATA::Util::TreeAutomata::Union(const TreeAutomata &o) {
    TreeAutomata result, o2;
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
    for (const auto &s : o.finalStates) {
        result.finalStates.insert(s + this->stateNum);
    }
    result.sim_reduce();
    return result;
}

VATA::Util::TreeAutomata VATA::Util::TreeAutomata::uniform(int n) {
    TreeAutomata aut;
    aut.name = "Uniform";
    aut.qubitNum = n;
    int pow_of_two = 1;
    int state_counter = 0;
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
  aut.finalStates.insert(0);
    aut.stateNum = pow_of_two;

    // aut.minimize();
    return aut;
}

VATA::Util::TreeAutomata VATA::Util::TreeAutomata::classical(int n) {
    TreeAutomata aut;
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
  aut.finalStates.insert(0);
    aut.stateNum = 2*n + 1;

    // aut.minimize();
    return aut;
}

VATA::Util::TreeAutomata VATA::Util::TreeAutomata::random(int n) {
    TreeAutomata aut;
    aut.name = "Random";
    aut.qubitNum = n;
    int pow_of_two = 1;
    int state_counter = 0;
    for (int level=1; level<=n; level++) {
        for (int i=0; i<pow_of_two; i++) {
            aut.transitions[{level}][{state_counter*2+1, state_counter*2+2}] = {state_counter};
            state_counter++;
        }
        pow_of_two *= 2;
    }
    for (int i=state_counter; i<=state_counter*2; i++) {
        aut.transitions[{rand()%5, rand()%5, rand()%5, rand()%5, 0}][{}].insert(i);
    }
  aut.finalStates.insert(0);
    aut.stateNum = state_counter*2 + 1;

    // aut.minimize();
    return aut;
}

VATA::Util::TreeAutomata VATA::Util::TreeAutomata::zero(int n) {
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
    aut.transitions[{1}][{2,1}] = {0};
    for (int level=2; level<=n; level++) {
        aut.transitions[{level}][{level*2-1, level*2-1}] = {level*2-3};
        aut.transitions[{level}][{level*2, level*2-1}] = {level*2-2};
    }
    aut.transitions[{0,0,0,0,0}][{}].insert(n*2-1);
    aut.transitions[{1,0,0,0,0}][{}].insert(n*2);
    aut.stateNum = n*2 + 1;

    // aut.minimize();
    return aut;
}

VATA::Util::TreeAutomata VATA::Util::TreeAutomata::classical_zero_one_zero(int n) {
    TreeAutomata aut;
    assert(n >= 2);
    aut.name = "Classical_Zero_One_Zero";
    aut.qubitNum = n + (n+1) + (n>=3) * (n-1);

    for (int level=1; level<=n; level++) {
        if (level >= 2)
            aut.transitions[{level}][{2*level - 1, 2*level - 1}] = {2*level - 3};
        aut.transitions[{level}][{2*level - 1, 2*level}] = {2*level - 2};
        aut.transitions[{level}][{2*level, 2*level - 1}] = {2*level - 2};
    }
    // aut.transitions[{1,0,0,0,0}][{}] = {2*n};
    // aut.transitions[{0,0,0,0,0}][{}] = {2*n - 1};
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
	aut.finalStates.insert(0);

    // aut.minimize();
    return aut;
}

void VATA::Util::TreeAutomata::swap_forward(const int k) {
    for (int next_k=k+1; next_k<=qubitNum; next_k++) {
        std::map<State, std::vector<std::pair<Symbol, StateVector>>> svsv;
        for (const auto &t : transitions) {
            auto &symbol = t.first;
            auto &in_outs = t.second;
            if (symbol.size() < 5 && symbol[0] == next_k) {
                assert(symbol.size() <= 2);
                for (const auto &in_out : in_outs) {
                    // assert(in_out.second.size() == 1);
                    // assert(t.second.size() == 1);
                    // assert(t.second.begin()->second.size() == 1);
                    // try {
                    //     ssv.at(*(t.second.begin()->second.begin()));
                    //     assert(false);
                    // } catch (...) {
                    for (const auto &s : in_out.second)
                        svsv[s /**(in_out.second.begin())*/].push_back(make_pair(symbol, in_out.first));
                    // }
                }
            }
        }
        std::vector<Symbol> to_be_removed2;
        TransitionMap to_be_removed, to_be_inserted;
        for (const auto &t : transitions) {
            if (t.first.size() < 5 && t.first[0] == k) {
                for (const auto &in_out : t.second) {
                    assert(in_out.first.size() == 2);
                    // assert(in_out.second.size() == 1);
                    for (const auto &ssv1 : svsv[in_out.first[0]]) {
                        for (const auto &ssv2 : svsv[in_out.first[1]]) {
                            to_be_removed[ssv1.first][ssv1.second].insert(in_out.first[0]);
                            to_be_removed[ssv2.first][ssv2.second].insert(in_out.first[1]);
                            to_be_inserted[t.first][{ssv1.second[0], ssv2.second[0]}].insert(stateNum++);
                            to_be_inserted[t.first][{ssv1.second[1], ssv2.second[1]}].insert(stateNum++);
                            for (const auto &s : in_out.second)
                                to_be_inserted[{next_k, ssv1.first[1], ssv2.first[1]}][{stateNum-2, stateNum-1}].insert(s); //(*in_out.second.begin()));
                        }
                    }
                }
                to_be_removed2.push_back(t.first);
            }
        }
        for (const auto &v : to_be_removed2)
            transitions.erase(v);
        for (const auto &t : to_be_removed) {
            for (const auto &in_out : t.second) {
                for (const auto &s : in_out.second)
                    transitions[t.first][in_out.first].erase(s); //*in_out.second.begin());
                if (transitions[t.first][in_out.first].empty())
                    transitions[t.first].erase(in_out.first);
                if (transitions[t.first].empty())
                    transitions.erase(t.first);
            }
        }
        for (const auto &t : to_be_inserted) {
            for (const auto &in_out : t.second) {
                for (const auto &s : in_out.second) {
                    transitions[t.first][in_out.first].insert(s);
                }
            }
        }
        // DO NOT reduce here.
    }
}

void VATA::Util::TreeAutomata::swap_backward(const int k) {
    for (int next_k=qubitNum; next_k>k; next_k--) {
      std::map<State, std::vector<std::pair<Symbol, StateVector>>> svsv;
        for (const auto &t : transitions) {
            auto &symbol = t.first;
            auto &in_outs = t.second;
            if (symbol.size() < 5 && symbol[0] == k) {
                assert(symbol.size() == 2);
                // print();
                // assert(t.second.size() == 1);
                for (const auto &in_out : in_outs) {
                    // assert(in_out.second.size() == 1);
                    // try {
                    //     svsv.at(*(in_out.second.begin()));
                    //     assert(false);
                    // } catch (...) {
                    for (const auto &s : in_out.second)
                        svsv[s /**(in_out.second.begin())*/].push_back(make_pair(symbol, in_out.first));
                    // }
                }
            }
        }
        std::vector<Symbol> to_be_removed2;
        TransitionMap to_be_removed, to_be_inserted;
        for (const auto &t : transitions) {
            if (t.first.size() < 5 && t.first[0] == next_k) {
                assert(t.first.size() == 3);
                for (const auto &in_out : t.second) {
                    assert(in_out.first.size() == 2);
                    // assert(in_out.second.size() == 1);
                    for (const auto &ssv1 : svsv[in_out.first[0]]) {
                        for (const auto &ssv2 : svsv[in_out.first[1]]) {
                            if (ssv1.first == ssv2.first) {
                                // assert(svsv[in_out.first[0]].first == svsv[in_out.first[1]].first);
                                to_be_removed[ssv1.first][ssv1.second].insert(in_out.first[0]);
                                to_be_removed[ssv2.first][ssv2.second].insert(in_out.first[1]);
                                to_be_inserted[{t.first[0], t.first[1]}][{ssv1.second[0], ssv2.second[0]}].insert(stateNum++);
                                to_be_inserted[{t.first[0], t.first[2]}][{ssv1.second[1], ssv2.second[1]}].insert(stateNum++);
                                assert(k == ssv1.first[0]);
                                for (const auto &s : in_out.second)
                                    to_be_inserted[ssv1.first][{stateNum-2, stateNum-1}].insert(s); //(*in_out.second.begin()));
                            }
                        }
                    }
                }
                to_be_removed2.push_back(t.first);
            }
        }
        for (const auto &v : to_be_removed2)
            transitions.erase(v);
        for (const auto &t : to_be_removed) {
            for (const auto &in_out : t.second) {
                for (const auto &s : in_out.second)
                    transitions[t.first][in_out.first].erase(s); //*in_out.second.begin());
                if (transitions[t.first][in_out.first].empty())
                    transitions[t.first].erase(in_out.first);
                if (transitions[t.first].empty())
                    transitions.erase(t.first);
            }
        }
        for (const auto &t : to_be_inserted) {
            for (const auto &in_out : t.second) {
                for (const auto &s : in_out.second) {
                    transitions[t.first][in_out.first].insert(s);
                }
            }
        }
        // DO NOT reduce here.
    }
}

void VATA::Util::TreeAutomata::value_restriction(int k, bool branch) {
    swap_forward(k);
    TransitionMap to_be_inserted;
    std::vector<Symbol> to_be_removed;
    for (const auto &t : transitions) {
        if (t.first.size() < 5 && t.first[0] == k) {
            to_be_removed.push_back(t.first);
            for (const auto &in_out : t.second) {
                assert(in_out.first.size() == 2);
                for (const auto &s : in_out.second) {
                    if (branch)
                        to_be_inserted[t.first][{in_out.first[1], in_out.first[1]}].insert(s);
                    else
                        to_be_inserted[t.first][{in_out.first[0], in_out.first[0]}].insert(s);
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
    sim_reduce();
}

void VATA::Util::TreeAutomata::fraction_simplication() {
  std::vector<StateVector> to_be_removed;
    TransitionMap to_be_inserted;
    for (const auto &t : transitions) {
        if (t.first.size() == 5) {
            to_be_removed.push_back(t.first);
            StateVector sv = t.first;
            int gcd = abs(t.first[0]);
            for (int i=1; i<4; i++)
                gcd = std::gcd(gcd, abs(t.first[i]));
            if (gcd > 0) {
                for (int i=0; i<4; i++)
                    sv[i] /= gcd;
                while (sv[4] >= 2 && gcd > 0 && (gcd&1) == 0) { // Notice the parentheses enclosing gcd&1 are very important! HAHA
                    gcd /= 2;
                    sv[4] -= 2;
                }
                for (int i=0; i<4; i++)
                    sv[i] *= gcd;
            } else {
                sv[4] = 0;
            }
            for (const auto &in_out : t.second) {
                for (const auto &s : in_out.second) {
                    to_be_inserted[sv][in_out.first].insert(s);
                }
            }
        }
    }

    for (const auto &t : to_be_removed) {
        transitions.erase(t);
    }
    for (const auto &t : to_be_inserted) {
        transitions.insert(t);
    }
}

namespace
{ // anonymous namespace
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

  std::string gpath_to_VATA = "";

  /** returns the path to VATA executable */
//   const std::string& get_vata_path()
//   {
//     // is it cached?
//     if (!gpath_to_VATA.empty()) return gpath_to_VATA;

//     // not cached, get it from ENV
//     const char* path = std::getenv("VATA_PATH");
//     if (nullptr == path) {
//       throw std::runtime_error("Cannot find environment variable VATA_PATH");
//     }

//     gpath_to_VATA = path;
//     return gpath_to_VATA;
//   }


  /** checks inclusion of two TAs */
//   bool check_inclusion(const std::string& lhsPath, const std::string& rhsPath)
//   {
//     std::string aux;
//     VATA::Util::ShellCmd(get_vata_path() + " incl " + lhsPath + " " + rhsPath, aux);
//     return (aux == "1\n");
//   }

  /** checks language equivalence of two TAs */
//   bool check_equal(const std::string& lhsPath, const std::string& rhsPath)
//   {
//     return check_inclusion(lhsPath, rhsPath) && check_inclusion(rhsPath, lhsPath);
//   }

//   bool check_equal_aut(
//       const VATA::Util::TreeAutomata& lhs,
//       const VATA::Util::TreeAutomata& rhs)
//   {
//     VATA::Serialization::TimbukSerializer serializer;
//     std::ofstream fileLhs("/tmp/automata1.txt");
//     fileLhs << serializer.Serialize(lhs);
//     fileLhs.close();

//     std::ofstream fileRhs("/tmp/automata2.txt");
//     fileRhs << serializer.Serialize(rhs);
//     fileRhs.close();

//     return check_equal("/tmp/automata1.txt", "/tmp/automata2.txt");
//   }
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

namespace {

  template <class Index>
  ExplicitLTS translate_to_lts_downward(
    const TreeAutomata& aut,
    size_t              numStates,
    Index&              stateIndex)
  {
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

  size_t count_aut_states(const VATA::Util::TreeAutomata& aut)
  {
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

  DiscontBinaryRelOnStates compute_down_sim(const VATA::Util::TreeAutomata& aut)
  {
    StateToIndexMap translMap;
    size_t stateCnt = 0;
    StateToIndexTranslWeak transl(translMap,
        [&stateCnt](const State&) {return stateCnt++;});

    size_t num_states = count_aut_states(aut);
    ExplicitLTS lts = translate_to_lts_downward(aut, num_states, transl);
    BinaryRelation ltsSim = lts.computeSimulation(num_states);
    return DiscontBinaryRelOnStates(ltsSim, translMap);
  }

  template <class Index>
  void reindex_aut_states(TreeAutomata& aut, Index& index)
  {
    StateSet newFinal;
    TransitionMap newTrans;

    for (const State& state : aut.finalStates) {
      newFinal.insert(index.at(state));
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

} // anonymous namespace

void VATA::Util::TreeAutomata::sim_reduce()
{
  DiscontBinaryRelOnStates sim = compute_down_sim(*this);

  // TODO: this is probably not optimal, we could probably get the mapping of
  // states for collapsing in a faster way
  sim.RestrictToSymmetric();       // sim is now an equivalence relation

  using StateToStateMap = std::unordered_map<State, State>;
  StateToStateMap collapseMap;
  sim.GetQuotientProjection(collapseMap);

  // TreeAutomata old = *this;
  reindex_aut_states(*this, collapseMap);

  // if (!check_equal_aut(*this, old)) {
  //   VATA_DEBUG("wrong simulation result!");
  //   VATA_DEBUG("old: " + old.ToString());
  //   VATA_DEBUG("new: " + this->ToString());
  //   VATA_DEBUG("simulation: " + sim.ToString());
  // }
}

void VATA::Util::TreeAutomata::print() {
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
    for (int i=0; i<stateNum; i++) {
        result += std::to_string(i) + " ";
        // result += stateNum.TranslateBwd(i) + " ";
    }
  // for_each(states.cbegin(), states.cend(),
  //  [&result](const std::string& sStr){ result += sStr + " ";});

  result += "\n";
  result += "Final States ";
    for (unsigned i : finalStates) {
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
