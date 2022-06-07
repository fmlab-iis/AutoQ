#include <vata/util/aut_description.hh>

#include <numeric>

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

void VATA::Util::TreeAutomata::determinize() {
	std::vector<StateSet> composite_set_id;
    TransitionMap transitions_new;

    /*******************************************************************/
    // Part 1: Generate composite sets from 0-arity symbols.
    for (const auto &f : transitions) {
        int arity = f.second.begin()->first.size();
        if (arity == 0) {
            const StateSet &ss = transitions.at(f.first).at({});
            try {
                int x = findIndex(composite_set_id, ss);
                transitions_new[f.first][StateVector({})] = StateSet({x});
            } catch (...) {
                int x = composite_set_id.size();
                transitions_new[f.first][StateVector({})] = StateSet({x});
                composite_set_id.push_back(ss);
            }
        }
    }
    /*******************************************************************/

    /*******************************************************************/
    // Part 2: Generate composite sets from (>= 1)-arity symbols.
    int old_composite_set_size, current_composite_set_size = 0;
    while (current_composite_set_size != static_cast<int>(composite_set_id.size())) {
        old_composite_set_size = current_composite_set_size;
        current_composite_set_size = composite_set_id.size();
        for (const auto &f : transitions) {
            int arity = f.second.begin()->first.size();
            if (arity >= 1) {
                StateVector sv(arity, 0); // enumerate all possible combinations of composite states
                bool overflow = false;
                do {
                    StateSet collected_RHS;
                    bool need_process = false;
                    for (int i=0; i<static_cast<int>(sv.size()); i++) {
                        if (sv[i] >= old_composite_set_size) {
                            need_process = true;
                            break;
                        }
                    }
                    if (need_process) {
                        for (const auto &in_out : transitions[f.first]) { // if this transition's input states are all contained
                            const auto &input = in_out.first;             // in the current combination of composite states, then
                            assert(static_cast<int>(input.size()) == arity);             // collect the states of RHS of this transition.
                            bool valid = true;
                            for (int i=0; i<arity; i++) {
                                if (composite_set_id[sv[i]].find(input[i]) == composite_set_id[sv[i]].end()) {
                                    valid = false;
                                    break;
                                }
                            }
                            if (valid) {
                                collected_RHS.insert(in_out.second.begin(), in_out.second.end());
                            }
                        }
                        if (!collected_RHS.empty()) {
                            try {
                                int x = findIndex(composite_set_id, collected_RHS); // may throw out_of_bound exception
                                transitions_new[f.first][sv] = StateSet({x});
                            } catch (...) {
                                int x = composite_set_id.size();
                                transitions_new[f.first][sv] = StateSet({x});
                                composite_set_id.push_back(collected_RHS);
                            }
                        }
                    }
                    sv[0]++;
                    for (int i=0; i<arity; i++) {
                        if (sv[i] == current_composite_set_size) {
                            if (i == arity - 1) {
                                overflow = true;
                                break;
                            } else {
                                sv[i] = 0;
                                sv[i+1]++;
                            }
                        } else break;
                    }
                } while (!overflow);
            }
        }
    }
    /*******************************************************************/

    /*******************************************************************/
    // Part 3: Automata reconstruction based on the refined partition.
    StateSet finalStates_new;
    for (unsigned i=0; i<composite_set_id.size(); i++) {
        StateSet temp; // should be empty
        const StateSet &cs = composite_set_id[i];
        set_intersection(cs.begin(), cs.end(), finalStates.begin(), finalStates.end(), inserter(temp, temp.begin()));
        if (!temp.empty()) {
            finalStates_new.insert(i);
        }
    }
    finalStates = finalStates_new;
    stateNum = composite_set_id.size();
    transitions = transitions_new;
    /*******************************************************************/
}

void VATA::Util::TreeAutomata::minimize() { // only for already determinized automata!
    /*******************************************************************/
    // Part 1: Partition states according to final states.
		std::vector<StateVector> partition;
    partition.push_back({}); // non-final states
    partition.push_back({}); // final states
    for (int i=0; i<stateNum; i++) { // TODO: can be optimized
        if (finalStates.find(i) == finalStates.end()) // non-final state
            partition[0].push_back(i);
        else
            partition[1].push_back(i);
    }
    /*******************************************************************/

    /*******************************************************************/
    // Part 2: Main loop of partition refinement.
		std::vector<int> state_to_partition_id;
    bool changed;
    do {
        changed = false;
				std::vector<StateVector> new_partition; // 有 .clear 的效果。
        state_to_partition_id = std::vector<int>(stateNum); // 有 .clear 的效果。
        for (unsigned i=0; i<partition.size(); i++) {
            for (const auto &s : partition[i])
                state_to_partition_id[s] = i;
        }
        for (const auto &cell : partition) { // original cell
					std::map<State, StateVector> refined; // 有 .clear 的效果。
            for (const auto &s : cell) { // state
                bool different_from_others = true;
                for (auto &new_cell : refined) { // check if s belongs to some refined cell
                    if (is_same_partition(state_to_partition_id, s, new_cell.first)) { // compare with "key" (head)
                        new_cell.second.push_back(s);
                        different_from_others = false;
                        break;
                    }
                }
                if (different_from_others)
                    refined[s] = StateVector(1, s);
            }
            /*************************************************
             * set the "changed" flag to true if the partition
             * changed in this cell. */
            if (refined.size() != 1)
                changed = true;
            else {
                for (const auto &new_cell : refined) // only one cell!
                    if (new_cell.second != cell) // the order should be the same
                        changed = true;
            }
            /************************************************/
            // push the refined partition in this cell finally
            for (const auto &new_cell : refined)
                new_partition.push_back(new_cell.second);
        }
        partition = new_partition;
    } while (changed);
    /*******************************************************************/

    /*******************************************************************/
    // Part 3: Automata reconstruction based on the refined partition.
    stateNum = partition.size();

    StateSet finalStates_new;
    for (const auto &s : finalStates)
        finalStates_new.insert(state_to_partition_id[s]);
    finalStates = finalStates_new;

    TransitionMap transitions_new;
    for (const auto &t : transitions) {
        for (const auto &t2 : t.second) {
            StateVector args = t2.first;
            for (unsigned i=0; i<args.size(); i++)
                args[i] = state_to_partition_id[args[i]];
            assert(t2.second.size() == 1);
            transitions_new[t.first][args] = StateSet({state_to_partition_id[*(t2.second.begin())]});
        }
    }
    transitions = transitions_new;
    /*******************************************************************/

    remove_useless(); // used in minimize() only.
}

void VATA::Util::TreeAutomata::remove_useless() { // only for already determinized automata!
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
            for (const auto &in_out : t.second) {
                bool input_traversed = in_out.first.empty();
                if (!input_traversed) {
                    input_traversed = true;
                    for (const auto &s : in_out.first)
                        input_traversed &= traversed[s];
                }
                if (input_traversed) {
                    assert(in_out.second.size() == 1);
                    traversed[*(in_out.second.begin())] = true;
                    transitions_remaining.at(t.first).erase(in_out.first);
                    if (transitions_remaining.at(t.first).empty())
                        transitions_remaining.erase(t.first);
                    changed = true;
                }
            }
        }
    } while(changed);
    for (const auto &t : transitions_remaining) {
        for (const auto &in_out : t.second) {
            transitions.at(t.first).erase(in_out.first);
            if (transitions.at(t.first).empty())
                transitions.erase(t.first);
        }
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
            for (const auto &in_out : t.second) {
                assert(in_out.second.size() == 1);
                if (traversed[*(in_out.second.begin())]) {
                    for (const auto &v : in_out.first)
                        traversed[v] = true;
                    transitions_remaining.at(t.first).erase(in_out.first);
                    if (transitions_remaining.at(t.first).empty())
                        transitions_remaining.erase(t.first);
                    changed = true;
                }
            }
        }
    } while(changed);
    for (const auto &t : transitions_remaining) {
        for (const auto &in_out : t.second) {
            transitions.at(t.first).erase(in_out.first);
            if (transitions.at(t.first).empty())
                transitions.erase(t.first);
        }
    }

    /*********************
     * Part 3: Renumbering
     *********************/
    TransitionMap transitions_new;
		std::map<int, int> stateOldToNew;
    for (const auto &t : transitions) {
        for (const auto &in_out : t.second) {
            StateVector sv;
            for (const auto &v : in_out.first) {
                try {
                    sv.push_back(stateOldToNew.at(v));
                } catch (...) {
                    stateOldToNew[v] = stateOldToNew.size();
                    sv.push_back(stateOldToNew.size()-1); //stateOldToNew.at(v));
                }
            }
            int dest;
            assert(in_out.second.size() == 1);
            try {
                dest = stateOldToNew.at(*(in_out.second.begin()));
            } catch (...) {
                stateOldToNew[*(in_out.second.begin())] = stateOldToNew.size();
                dest = stateOldToNew.size() - 1;
            }
            transitions_new[t.first].insert(make_pair(sv, StateSet({dest})));
        }
    }
    transitions = transitions_new;
    StateSet finalStates_new;
    for (const auto &s : finalStates) {
        finalStates_new.insert(stateOldToNew[s]);
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

    determinize();
    minimize();
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

    determinize();
    minimize();
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
    fraction_simplication();
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

    determinize();
    minimize();
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

    determinize();
    minimize();
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

    determinize();
    minimize();
}

VATA::Util::TreeAutomata VATA::Util::TreeAutomata::binary_operation(const TreeAutomata &o, bool add) {
    TreeAutomata result;
    result.name = name;
    result.qubitNum = qubitNum;
    result.stateNum *= o.stateNum;

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
                ss.insert((*(itt->second.begin())) * o.stateNum + (*(itt2->second.begin())));
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
            result.transitions[in][{}].insert((*(it->second.begin()->second.begin())) * o.stateNum + (*(it2t->second.begin()->second.begin())));
        }
    }

    result.determinize();
    result.minimize();
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
    for (const auto &s : o.finalStates)
	    result.finalStates.insert(s + this->stateNum);

    result.determinize();
    result.minimize();
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

    // aut.determinize();
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

    // aut.determinize();
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

    // aut.determinize();
    // aut.minimize();
    return aut;
}

VATA::Util::TreeAutomata VATA::Util::TreeAutomata::zero(int n) {
    TreeAutomata aut;
    aut.name = "Zero";
    aut.qubitNum = n;
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
    aut.transitions[{1,0,0,0,0}][{}].insert(state_counter);
    for (int i=state_counter+1; i<=state_counter*2; i++) {
        aut.transitions[{0,0,0,0,0}][{}].insert(i);
    }
	aut.finalStates.insert(0);
    aut.stateNum = state_counter*2 + 1;

    aut.determinize();
    aut.minimize();
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
                    assert(in_out.second.size() == 1);
                    // assert(t.second.size() == 1);
                    // assert(t.second.begin()->second.size() == 1);
                    // try {
                    //     ssv.at(*(t.second.begin()->second.begin()));
                    //     assert(false);
                    // } catch (...) {
                    svsv[*(in_out.second.begin())].push_back(make_pair(symbol, in_out.first));
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
                    assert(in_out.second.size() == 1);
                    for (const auto &ssv1 : svsv[in_out.first[0]]) {
                        for (const auto &ssv2 : svsv[in_out.first[1]]) {
                            to_be_removed[ssv1.first][ssv1.second].insert(in_out.first[0]);
                            to_be_removed[ssv2.first][ssv2.second].insert(in_out.first[1]);
                            to_be_inserted[t.first][{ssv1.second[0], ssv2.second[0]}].insert(stateNum++);
                            to_be_inserted[t.first][{ssv1.second[1], ssv2.second[1]}].insert(stateNum++);
                            to_be_inserted[{next_k, ssv1.first[1], ssv2.first[1]}][{stateNum-2, stateNum-1}].insert((*in_out.second.begin()));
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
                transitions[t.first][in_out.first].erase(*in_out.second.begin());
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
        determinize();
        minimize();
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
                    assert(in_out.second.size() == 1);
                    // try {
                    //     svsv.at(*(in_out.second.begin()));
                    //     assert(false);
                    // } catch (...) {
                        svsv[*(in_out.second.begin())].push_back(make_pair(symbol, in_out.first));
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
                    assert(in_out.second.size() == 1);
                    for (const auto &ssv1 : svsv[in_out.first[0]]) {
                        for (const auto &ssv2 : svsv[in_out.first[1]]) {
                            if (ssv1.first == ssv2.first) {
                                // assert(svsv[in_out.first[0]].first == svsv[in_out.first[1]].first);
                                to_be_removed[ssv1.first][ssv1.second].insert(in_out.first[0]);
                                to_be_removed[ssv2.first][ssv2.second].insert(in_out.first[1]);
                                to_be_inserted[{t.first[0], t.first[1]}][{ssv1.second[0], ssv2.second[0]}].insert(stateNum++);
                                to_be_inserted[{t.first[0], t.first[2]}][{ssv1.second[1], ssv2.second[1]}].insert(stateNum++);
                                assert(k == ssv1.first[0]);
                                to_be_inserted[ssv1.first][{stateNum-2, stateNum-1}].insert((*in_out.second.begin()));
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
                transitions[t.first][in_out.first].erase(*in_out.second.begin());
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
        determinize();
        minimize();
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
    determinize();
    minimize();
    swap_backward(k);
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
	// 	[&result](const std::string& sStr){ result += sStr + " ";});

	result += "\n";
	result += "Final States ";
    for (unsigned i : finalStates) {
        result += std::to_string(i) + " ";
        // result += stateNum.TranslateBwd(i) + " ";
    }
	// for_each(finalStates.cbegin(), finalStates.cend(),
	// 	[&result](const std::string& fsStr){ result += fsStr + " ";});

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
