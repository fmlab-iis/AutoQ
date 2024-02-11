#include <autoq/aut_description.hh>
#include <autoq/complex/complex.hh>
#include <autoq/symbol/concrete.hh>
#include <autoq/symbol/symbolic.hh>
#include <autoq/symbol/predicate.hh>
#include <numeric> // used in std::numeric_limits
#include <chrono> // used in remove_useless
#include <queue> // used in remove_useless

template <typename Symbol>
void AUTOQ::Automata<Symbol>::state_renumbering() {
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
void AUTOQ::Automata<Symbol>::omega_multiplication(int rotation) requires not_predicate<Symbol> {
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
void AUTOQ::Automata<Symbol>::divide_by_the_square_root_of_two() requires not_predicate<Symbol> {
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
void AUTOQ::Automata<Symbol>::branch_restriction(int k, bool positive_has_value) requires not_predicate<Symbol> {
    auto start = std::chrono::steady_clock::now();
    State num_of_states = stateNum;
    if (stateNum > std::numeric_limits<State>::max() / 2)
        throw std::overflow_error(AUTOQ_LOG_PREFIX + "[ERROR] The number of states is too large.");
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
void AUTOQ::Automata<Symbol>::semi_determinize() requires not_predicate<Symbol> {
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
void AUTOQ::Automata<Symbol>::semi_undeterminize() requires not_predicate<Symbol> {
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
AUTOQ::Automata<Symbol> AUTOQ::Automata<Symbol>::binary_operation(const AUTOQ::Automata<Symbol> &o, bool add) requires not_predicate<Symbol> {
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
        throw std::overflow_error(AUTOQ_LOG_PREFIX + "[ERROR] The number of states after multiplication is too large.");

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
    if (this->vars != o.vars || this->constraints != o.constraints) {
        throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] The two variable sets or constraints in binary_operation are not exactly the same.");
    }
    result.vars = this->vars;
    result.constraints = this->constraints;
    auto end = std::chrono::steady_clock::now();
    binop_time += end - start;
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
    return result;
}
template <typename Symbol>
AUTOQ::Automata<Symbol> AUTOQ::Automata<Symbol>::operator+(const Automata &o) requires not_predicate<Symbol> {
    return binary_operation(o, true);
}
template <typename Symbol>
AUTOQ::Automata<Symbol> AUTOQ::Automata<Symbol>::operator-(const Automata &o) requires not_predicate<Symbol> {
    return binary_operation(o, false);
}
template <typename Symbol>
AUTOQ::Automata<Symbol> AUTOQ::Automata<Symbol>::operator*(int c) requires not_predicate<Symbol> {
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
void AUTOQ::Automata<Symbol>::fraction_simplification() requires not_predicate<Symbol> {
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

template <>
void AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::k_unification() {
    // Step 1: Get the maximum k.
    boost::multiprecision::cpp_int k = INT_MIN;
    for (const auto &t : transitions) {
        const SymbolTag &symbol_tag = t.first;
        if (symbol_tag.is_leaf()) {
            auto c = symbol_tag.symbol().complex;
            c.fraction_simplification();
            auto k2 = c.max_k();
            if (k < k2)
                k = k2;
        }
    }

    // Step 2: Adjust all complex numbers' k to its maximum, and then directly remove them.
    std::vector<SymbolTag> to_be_removed;
    TransitionMap to_be_inserted;
    for (const auto &t : transitions) {
        const SymbolTag &s = t.first;
        if (s.is_leaf()) {
            SymbolTag symbol_tag = s;
            symbol_tag.symbol().complex.adjust_k_and_discard(k);
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

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Predicate>;
