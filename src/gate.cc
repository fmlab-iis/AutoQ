#include <functional>
#include <boost/rational.hpp>

#include "autoq/util/util.hh"
#include "autoq/aut_description.hh"

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wold-style-cast"
#include <boost/multiprecision/cpp_int.hpp>
#pragma GCC diagnostic pop


// #define TO_QASM
#define QASM_FILENAME "circuit.qasm"
// OPENQASM 2.0;
// include "qelib1.inc";
// qreg qubits[?];

#define L(s1, s2) (stateNum + (s1) * stateNum + (s2))
#define R(s1, s2) (stateNum + stateNum * stateNum + (s1) * stateNum + (s2))
template <typename Symbol>
void AUTOQ::Automata<Symbol>::General_Single_Qubit_Gate(int t, const std::function<Symbol(const Symbol&, const Symbol&)> &u1u2, const std::function<Symbol(const Symbol&, const Symbol&)> &u3u4) {
    AUTOQ::Automata<Symbol> result;
    result.name = name;
    result.qubitNum = qubitNum;
    result.isTopdownDeterministic = isTopdownDeterministic; // IMPORTANT: Avoid missing copying new fields afterwards.
    result.finalStates = finalStates;
    result.hasLoop = hasLoop; // IMPORTANT: Avoid missing copying new fields afterwards.
    result.vars = vars; // IMPORTANT: Avoid missing copying new fields afterwards.
    result.constraints = constraints; // IMPORTANT: Avoid missing copying new fields afterwards.

    bool overflow = (stateNum > (std::numeric_limits<State>::max()-stateNum) / stateNum / 2); // want: 2 * stateNum^2 + stateNum <= max
    if (overflow)
        THROW_AUTOQ_ERROR("The number of states after multiplication is too large.");
    // s < stateNum -> s
    // (s1, s2, L) -> stateNum + s1 * stateNum + s2
    // (s1, s2, R) -> stateNum + stateNum^2 + s1 * stateNum + s2 -> max == 2 * stateNum^2 + stateNum - 1

    // We assume here transitions are ordered by symbols.
    // x_i are placed in the beginning, and leaves are placed in the end.
    // This traversal method is due to efficiency.
    auto it = transitions.begin(); // global pointer
    for (; it != transitions.end(); it++) { // iterate over all internal transitions of symbol < t
        assert(it->first.is_internal());
        if (it->first.symbol().qubit() >= t) break;
        result.transitions.insert(*it);
    }

    std::vector<bool> possible_next_level_states(R(stateNum-1, stateNum-1) + 1);
    assert(it->first.symbol().qubit() == t); // iterate over all internal transitions of symbol == t
    for (; it != transitions.end(); it++) {
        if (it->first.is_leaf() || it->first.symbol().qubit() > t) break;
        auto &ref1 = result.transitions[it->first];
        for (const auto &out_ins : it->second) {
            auto &ref2 = ref1[out_ins.first];
            for (const auto &in : out_ins.second) {
                assert(in.size() == 2);
                ref2.insert({L(in.at(0), in.at(1)), R(in.at(0), in.at(1))});
                possible_next_level_states[L(in.at(0), in.at(1))] = true;
                possible_next_level_states[R(in.at(0), in.at(1))] = true;
            }
        }
    }

    auto head = it;
    std::map<State, std::map<Tag, std::map<Symbol, std::vector<StateVector>>>> qcfi;
    std::vector<bool> possible_previous_level_states = possible_next_level_states;
    for (; it != transitions.end(); it++) { // iterate over all internal transitions of symbol > t
        if (it->first.is_leaf()) break; // assert internal transition
        auto qubit = it->first.symbol().qubit();
        assert(qubit > t);
        if (qubit != head->first.symbol().qubit()) { // change layer
            head = it;
            possible_previous_level_states = possible_next_level_states;
        }
        for (auto it2 = head; it2 != transitions.end(); it2++) {
            if (it2->first.is_leaf()) break; // another internal transition
            if (it2->first.symbol().qubit() != qubit) break; // ensure that the two symbols have the same qubit.
            assert(it->first.symbol() == it2->first.symbol());
            auto color_intersection = it->first.tag() & it2->first.tag();
            if (color_intersection == 0) continue;  // ignore empty colors
            for (const auto &out_ins1 : it->second) {
                const auto &top1 = out_ins1.first;
                // assert(out_ins1.first.size() == 2);
                for (const auto &out_ins2 : it2->second) {
                    const auto &top2 = out_ins2.first;
                    // assert(out_ins2.first.size() == 2);
                    if (hasLoop || possible_previous_level_states[L(top1, top2)]) {
                        auto &ref = qcfi[L(top1, top2)][color_intersection][it->first.symbol()];
                        for (const auto &in1 : out_ins1.second) {
                            for (const auto &in2 : out_ins2.second) {
                                ref.push_back({L(in1.at(0), in2.at(0)), L(in1.at(1), in2.at(1))});
                            }
                        }
                    }
                    if (hasLoop || possible_previous_level_states[R(top1, top2)]) {
                        auto &ref = qcfi[R(top1, top2)][color_intersection][it->first.symbol()];
                        for (const auto &in1 : out_ins1.second) {
                            for (const auto &in2 : out_ins2.second) {
                                ref.push_back({R(in1.at(0), in2.at(0)), R(in1.at(1), in2.at(1))});
                            }
                        }
                    }
                }
            }
        }
        if (std::next(it, 1) == transitions.end() || std::next(it, 1)->first.is_leaf() || qubit != std::next(it, 1)->first.symbol().qubit()) { // this layer is finished!
            for (const auto &q_ : qcfi) {
                for (const auto &c_ : q_.second) {
                    for (const auto &f_ : c_.second) {
                        result.transitions[{f_.first, c_.first}][q_.first].insert(f_.second.begin(), f_.second.end());
                        for (const auto &i : f_.second) {
                            for (const auto &s : i)
                                possible_next_level_states[s] = true;
                        }
                    }
                }
            }
            qcfi.clear(); // = std::map<State, std::map<Tag, std::vector<std::pair<Symbol, StateVector>>>>();
        }
    }

    head = it;
    possible_previous_level_states = possible_next_level_states;
    qcfi.clear(); // = std::map<State, std::map<Tag, std::vector<std::pair<Symbol, StateVector>>>>(); // may be redundant due to LINE 270
    for (; it != transitions.end(); it++) { // iterate over all leaf transitions
        assert(it->first.is_leaf()); // assert leaf transition
        for (auto it2 = head; it2 != transitions.end(); it2++) {
            assert(it2->first.is_leaf()); // another leaf transition
            auto color_intersection = it->first.tag() & it2->first.tag();
            if (color_intersection == 0) continue;  // ignore empty colors
            for (const auto &out_ins1 : it->second) {
                const auto &top1 = out_ins1.first;
                // assert(in_out1.first.size() == 0);
                for (const auto &out_ins2 : it2->second) {
                    const auto &top2 = out_ins2.first;
                    if (hasLoop || possible_previous_level_states[L(top1, top2)]) {
                        qcfi[L(top1, top2)][color_intersection][u1u2(it->first.symbol(), it2->first.symbol())].push_back({});
                    }
                    if (hasLoop || possible_previous_level_states[R(top1, top2)]) {
                        qcfi[R(top1, top2)][color_intersection][u3u4(it->first.symbol(), it2->first.symbol())].push_back({});
                    }
                }
            }
        }
    }
    for (const auto &q_ : qcfi) {
        for (const auto &c_ : q_.second) {
            for (const auto &f_ : c_.second) { // f_.second := a lot of input vectors
                result.transitions[{f_.first, c_.first}][q_.first].insert(f_.second.begin(), f_.second.end());
            }
        }
    }
    result.stateNum = R(stateNum-1, stateNum-1) + 1;
    // result.state_renumbering();
    result.reduce();
    *this = result;
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::General_Controlled_Gate(int c, int t, const std::function<Symbol(const Symbol&, const Symbol&)> &u1u2, const std::function<Symbol(const Symbol&, const Symbol&)> &u3u4) {
    if (c <= t) {
        THROW_AUTOQ_ERROR("We require c > t here.");
    }
    General_Controlled_Gate(c, c, t, u1u2, u3u4);
}
template <typename Symbol>
void AUTOQ::Automata<Symbol>::General_Controlled_Gate(int c, int c2, int t, const std::function<Symbol(const Symbol&, const Symbol&)> &u1u2, const std::function<Symbol(const Symbol&, const Symbol&)> &u3u4) {
    General_Controlled_Gate({c, c2}, t, u1u2, u3u4);
}
#define L2(s1, s2) (2*stateNum + (s1) * stateNum + (s2))
#define R2(s1, s2) (2*stateNum + stateNum * stateNum + (s1) * stateNum + (s2))
template <typename Symbol>
void AUTOQ::Automata<Symbol>::General_Controlled_Gate(std::set<int> cs, int t, const std::function<Symbol(const Symbol&, const Symbol&)> &u1u2, const std::function<Symbol(const Symbol&, const Symbol&)> &u3u4) {
    auto minC = *cs.begin(); // To find the minimum value in a std::set in C++, you can use the begin() iterator since std::set is always sorted in ascending order.

    AUTOQ::Automata<Symbol> result;
    result.name = name;
    result.qubitNum = qubitNum;
    result.isTopdownDeterministic = isTopdownDeterministic; // IMPORTANT: Avoid missing copying new fields afterwards.
    result.finalStates = finalStates;
    result.hasLoop = hasLoop; // IMPORTANT: Avoid missing copying new fields afterwards.
    result.vars = vars; // IMPORTANT: Avoid missing copying new fields afterwards.
    result.constraints = constraints; // IMPORTANT: Avoid missing copying new fields afterwards.

    bool overflow = (stateNum > (std::numeric_limits<State>::max()/2 - stateNum) / stateNum); // want: 2 * stateNum^2 + 2 * stateNum <= max
    if (overflow)
        THROW_AUTOQ_ERROR("The number of states after multiplication is too large.");
    // s < stateNum -> s + stateNum (in U)
    // s < stateNum -> s (in the original)
    // (s1, s2, L) -> 2 * stateNum + s1 * stateNum + s2
    // (s1, s2, R) -> 2 * stateNum + stateNum^2 + s1 * stateNum + s2 -> max == 2 * stateNum^2 + 2 * stateNum - 1

    // We assume here transitions are ordered by symbols.
    // x_i are placed in the beginning, and leaves are placed in the end.
    // This traversal method is due to efficiency.
    auto it = transitions.begin(); // global pointer, useless initial value only for declaring its type
    bool it_has_been_assigned = false;
    for (auto it0 = transitions.begin(); it0 != transitions.end(); it0++) { // iterate over all internal transitions of symbol < t
        if (it0->first.symbol().is_leaf()) {
            result.transitions.insert(*it0);
        } else if (it0->first.symbol().qubit() < t) { // must be internal
            if (it0->first.symbol().qubit() < minC) {
                result.transitions.insert(*it0);
            } else if (it0->first.symbol().qubit() == minC) {
                auto &ref = result.transitions[it0->first];
                for (const auto &[out, ins] : it0->second) {
                    auto &ref2 = ref[out];
                    for (const auto &in : ins) {
                        assert(in.size() == 2);
                        ref2.insert({in.at(0), in.at(1)+stateNum});
                    }
                }
            } else { // if (it0->first.symbol().qubit() > minC)
                result.transitions.insert(*it0); // the original part
                // The following is the U part.
                auto &ref = result.transitions[it0->first];
                bool qubit_is_NOT_a_control_qubit = cs.find(static_cast<int>(it0->first.symbol().qubit())) == cs.end();
                for (const auto &[out, ins] : it0->second) {
                    auto &ref2 = ref[out+stateNum]; // offset
                    for (const auto &in : ins) {
                        assert(in.size() == 2);
                        ref2.insert({in.at(0) + qubit_is_NOT_a_control_qubit * stateNum, in.at(1)+stateNum}); // offset
                    }
                }
            }
            // TODO: A potential improvement is to also record all used bottom states
            //       at level minC as all possible top states at level minC+1, and so
            //       on, until level t, to avoid generating useless transitions.
        }
        if (!it_has_been_assigned && it0->first.symbol().qubit() >= t) {
            it = it0;
            it_has_been_assigned = true;
        }
    }

    std::vector<bool> possible_next_level_states(R2(stateNum-1, stateNum-1) + 1);
    assert(it->first.symbol().qubit() == t); // iterate over all internal transitions of symbol == t
    for (; it != transitions.end(); it++) {
        if (it->first.is_leaf() || it->first.symbol().qubit() > t) break;
        assert(it->first.symbol().qubit() == t);
        if (minC < t) {
            result.transitions.insert(*it);
            // TODO: consider only the top states in possible_previous_level_states
            //       if they are recorded in the previous level.
        }
        auto &ref1 = result.transitions[it->first];
        for (const auto &out_ins : it->second) {
            auto &ref2 = ref1[out_ins.first + ((minC < t) ? stateNum : 0)];
            // TODO: consider only the top states in possible_previous_level_states
            //       if they are recorded in the previous level.
            for (const auto &in : out_ins.second) {
                assert(in.size() == 2);
                ref2.insert({L2(in.at(0), in.at(1)), R2(in.at(0), in.at(1))});
                possible_next_level_states[L2(in.at(0), in.at(1))] = true;
                possible_next_level_states[R2(in.at(0), in.at(1))] = true;
            }
        }
    }

    auto head = it;
    std::map<State, std::map<Tag, std::map<Symbol, std::vector<StateVector>>>> qcfi;
    std::vector<bool> possible_previous_level_states = possible_next_level_states;
    for (; it != transitions.end(); it++) { // iterate over all internal transitions of symbol > t
        if (it->first.is_leaf()) break; // assert internal transition
        int qubit = static_cast<int>(it->first.symbol().qubit());
        assert(qubit > t);
        if (qubit != head->first.symbol().qubit()) { // change layer
            head = it;
            possible_previous_level_states = possible_next_level_states;
        }
        for (auto it2 = head; it2 != transitions.end(); it2++) {
            if (it2->first.is_leaf()) break; // another internal transition
            if (it2->first.symbol().qubit() != qubit) break; // ensure that the two symbols have the same qubit.
            assert(it->first.symbol() == it2->first.symbol());
            auto color_intersection = it->first.tag() & it2->first.tag();
            if (color_intersection == 0) continue;  // ignore empty colors
            for (const auto &out_ins1 : it->second) {
                const auto &top1 = out_ins1.first;
                // assert(out_ins1.first.size() == 2);
                for (const auto &out_ins2 : it2->second) {
                    const auto &top2 = out_ins2.first;
                    // assert(out_ins2.first.size() == 2);
                    bool qubit_is_NOT_a_control_qubit = cs.find(qubit) == cs.end();
                    if (hasLoop || possible_previous_level_states[L2(top1, top2)]) {
                        auto &ref = qcfi[L2(top1, top2)][color_intersection][it->first.symbol()];
                        if (qubit_is_NOT_a_control_qubit) {
                            for (const auto &in1 : out_ins1.second) {
                                for (const auto &in2 : out_ins2.second) {
                                    ref.push_back({L2(in1.at(0), in2.at(0)), L2(in1.at(1), in2.at(1))});
                                }
                            }
                        } else { // if (qubit_is_a_control_qubit)
                            for (const auto &in1 : out_ins1.second) {
                                for (const auto &in2 : out_ins2.second) {
                                    ref.push_back({in1.at(0), L2(in1.at(1), in2.at(1))});
                                }
                            }
                        }
                    }
                    if (hasLoop || possible_previous_level_states[R2(top1, top2)]) {
                        auto &ref = qcfi[R2(top1, top2)][color_intersection][it->first.symbol()];
                        if (qubit_is_NOT_a_control_qubit) {
                            for (const auto &in1 : out_ins1.second) {
                                for (const auto &in2 : out_ins2.second) {
                                    ref.push_back({R2(in1.at(0), in2.at(0)), R2(in1.at(1), in2.at(1))});
                                }
                            }
                        } else { // if (qubit_is_a_control_qubit)
                            for (const auto &in1 : out_ins1.second) {
                                for (const auto &in2 : out_ins2.second) {
                                    ref.push_back({in2.at(0), R2(in1.at(1), in2.at(1))});
                                }
                            }
                        }
                    }
                }
            }
            if (qubit > minC) {
                for (const auto &out_ins : it->second) {
                    const auto &top = out_ins.first;
                    if (hasLoop || possible_previous_level_states[top] || minC < t) {
                        // TODO: can remove (minC < t) if possible_previous_level_states are well-constructed in this case
                        auto &ref = qcfi[top][color_intersection][it->first.symbol()];
                        ref.insert(ref.end(), out_ins.second.begin(), out_ins.second.end());
                    }
                }
                for (const auto &out_ins : it2->second) {
                    const auto &top = out_ins.first;
                    if (hasLoop || possible_previous_level_states[top] || minC < t) {
                        // TODO: can remove (minC < t) if possible_previous_level_states are well-constructed in this case
                        auto &ref = qcfi[top][color_intersection][it2->first.symbol()]; // can also use it->first.symbol()
                        ref.insert(ref.end(), out_ins.second.begin(), out_ins.second.end());
                    }
                }
            }
        }
        if (std::next(it, 1) == transitions.end() || std::next(it, 1)->first.is_leaf() || qubit != std::next(it, 1)->first.symbol().qubit()) { // this layer is finished!
            for (const auto &q_ : qcfi) {
                for (const auto &c_ : q_.second) {
                    for (const auto &f_ : c_.second) {
                        result.transitions[{f_.first, c_.first}][q_.first].insert(f_.second.begin(), f_.second.end());
                        for (const auto &i : f_.second) {
                            for (const auto &s : i)
                                possible_next_level_states[s] = true;
                        }
                    }
                }
            }
            qcfi.clear(); // = std::map<State, std::map<Tag, std::vector<std::pair<Symbol, StateVector>>>>();
        }
    }

    head = it;
    possible_previous_level_states = possible_next_level_states;
    qcfi.clear(); // = std::map<State, std::map<Tag, std::vector<std::pair<Symbol, StateVector>>>>(); // may be redundant due to LINE 270
    for (; it != transitions.end(); it++) { // iterate over all leaf transitions
        assert(it->first.is_leaf()); // assert leaf transition
        for (auto it2 = head; it2 != transitions.end(); it2++) {
            assert(it2->first.is_leaf()); // another leaf transition
            auto color_intersection = it->first.tag() & it2->first.tag();
            if (color_intersection == 0) continue;  // ignore empty colors
            for (const auto &out_ins1 : it->second) {
                const auto &top1 = out_ins1.first;
                // assert(in_out1.first.size() == 0);
                for (const auto &out_ins2 : it2->second) {
                    const auto &top2 = out_ins2.first;
                    if (hasLoop || possible_previous_level_states[L2(top1, top2)]) {
                        qcfi[L2(top1, top2)][color_intersection][u1u2(it->first.symbol(), it2->first.symbol())].push_back({});
                    }
                    if (hasLoop || possible_previous_level_states[R2(top1, top2)]) {
                        qcfi[R2(top1, top2)][color_intersection][u3u4(it->first.symbol(), it2->first.symbol())].push_back({});
                    }
                }
            }
        }
    }
    for (const auto &q_ : qcfi) {
        for (const auto &c_ : q_.second) {
            for (const auto &f_ : c_.second) { // f_.second := a lot of input vectors
                result.transitions[{f_.first, c_.first}][q_.first].insert(f_.second.begin(), f_.second.end());
            }
        }
    }
    result.stateNum = R2(stateNum-1, stateNum-1) + 1;
    // Notice that we cannot do operations including state_renumbering() here
    // since this function may be used as a subroutine in another gate.
    *this = result;
}

#define queryTopID(oldID, newID) \
    State newID = oldID + stateNum;/*
    // {   \
    //     auto it = topStateMap.find(oldID);    \
    //     if (it == topStateMap.end())    \
    //         newID = oldID;    \
    //     else    \
    //         newID = it->second; \
    // }*/
#define queryChildID(oldID, newID) \
    State newID = oldID + stateNum;/*
    // {   \
    //     auto it = childStateMap.find(oldID);    \
    //     if (it == childStateMap.end())    \
    //         newID = oldID;    \
    //     else    \
    //         newID = it->second; \
    // }*/
template <typename Symbol>
void AUTOQ::Automata<Symbol>::Diagonal_Gate(int t, const std::function<void(Symbol*)> &multiply_by_c0, const std::function<void(Symbol*)> &multiply_by_c1) {
    TopDownTransitions transitions2;
    std::map<State, int> topStateIsLeftOrRight, childStateIsLeftOrRight; // 0b10: original tree, 0b01: copied tree, 0b11: both trees
    // std::map<State, State> topStateMap, childStateMap;
    // If a state has only one tree, then its id does not change. In this case, it is not present in this map.
    // If a state has two trees, then it presents in this map and its value is the id in the copied tree.

    // Convert from TopDownTransitions to InternalTopDownTransitions.
    InternalTopDownTransitions internalTransitions(qubitNum + 1 + (hasLoop ? 1 : 0)); // only contains qubits from t to the bottom
    TopDownTransitions leafTransitions;
    for (const auto &tr : transitions) {
        if (tr.first.is_internal()) {
            if (tr.first.symbol().qubit() < t)
                transitions2[tr.first] = tr.second;
            else
                internalTransitions[static_cast<int>(tr.first.symbol().qubit())][tr.first.tag()] = tr.second;
        } else {
            leafTransitions[tr.first] = tr.second;
        }
    }

    // Assume the initial state numbers are already compact.
    for (int q = t; q <= qubitNum + (hasLoop ? 1 : 0); q++) {
        if (q == t) {
            /* Construct childStateIsLeftOrRight. */
            for (const auto &tag_outins : internalTransitions[q]) {
                for (const auto &out_ins : tag_outins.second) {
                    for (const auto &in : out_ins.second) {
                        assert(in.size() == 2);
                        childStateIsLeftOrRight[in[0]] |= 0b10;
                        childStateIsLeftOrRight[in[1]] |= 0b01;
                    }
                }
            }
            /**************************************/
            /* Construct childStateMap. */
            // for (const auto &kv : childStateIsLeftOrRight) {
            //     if (kv.second == 0b11) {
            //         childStateMap[kv.first] = stateNum;
            //         stateNum++;
            //     }
            // }
            /****************************/
            for (const auto &tag_outins : internalTransitions[q]) {
                auto &ref = transitions2[{Symbol(q), tag_outins.first}];
                for (const auto &out_ins : tag_outins.second) {
                    const auto &top = out_ins.first;
                    auto &reftop = ref[top];
                    for (const auto &in : out_ins.second) {
                        assert(in.size() == 2);
                        queryChildID(in[1], newIn1);
                        reftop.insert({in[0], newIn1});
                    }
                }
            }
        } else { // if (q > t) {
            /* Construct childStateIsLeftOrRight. */
            for (const auto &tag_outins : internalTransitions[q]) {
                for (const auto &out_ins : tag_outins.second) {
                    const auto &top = out_ins.first;
                    auto val = topStateIsLeftOrRight[top];
                    for (const auto &in : out_ins.second) {
                        assert(in.size() == 2);
                        childStateIsLeftOrRight[in[0]] |= val;
                        childStateIsLeftOrRight[in[1]] |= val;
                    }
                }
            }
            /**************************************/
            /* Construct childStateMap. */
            // for (const auto &kv : childStateIsLeftOrRight) {
            //     if (kv.second == 0b11) {
            //         childStateMap[kv.first] = stateNum;
            //         stateNum++;
            //     }
            // }
            /****************************/
            for (const auto &tag_outins : internalTransitions[q]) {
                auto &ref = transitions2[{Symbol(q), tag_outins.first}];
                for (const auto &out_ins : tag_outins.second) {
                    const auto &top = out_ins.first;
                    auto val = topStateIsLeftOrRight[top];
                    if (val & 0b10) {
                        ref[top] = out_ins.second;
                    }
                    queryTopID(top, newTop);
                    auto &refnewTop = ref[newTop];
                    if (val & 0b01) {
                        for (const auto &in : out_ins.second) {
                            assert(in.size() == 2);
                            queryChildID(in[0], newIn0);
                            queryChildID(in[1], newIn1);
                            refnewTop.insert({newIn0, newIn1});
                        }
                    }
                }
            }
        }
        /**********************************************/
        topStateIsLeftOrRight = childStateIsLeftOrRight;
        childStateIsLeftOrRight.clear();
        // topStateMap = childStateMap;
        // childStateMap.clear();
        /**********************************************/
    }
    for (const auto &tr : leafTransitions) {
        for (const auto &out_ins : tr.second) {
            const auto &top = out_ins.first;
            auto val = topStateIsLeftOrRight[top];
            if (val & 0b10) {
                SymbolTag symbol_tag = tr.first;
                multiply_by_c0(&symbol_tag.symbol());
                transitions2[symbol_tag][top].insert({{}});
            }
            if (val & 0b01) {
                SymbolTag symbol_tag = tr.first;
                multiply_by_c1(&symbol_tag.symbol());
                queryTopID(top, newTop);
                transitions2[symbol_tag][newTop].insert({{}});
            }
        }
    }
    transitions = transitions2;
    stateNum *= 2;
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::X(int t) {
    #ifdef TO_QASM
        system(("echo 'x qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    for (auto &tr : transitions) {
        if (tr.first.is_internal() && tr.first.symbol().qubit() == t) {
            for (auto &out_ins : tr.second) {
                std::set<StateVector> ins2;
                for (const auto &in : out_ins.second) {
                    assert(in.size() == 2);
                    ins2.insert({in[1], in[0]});
                }
                out_ins.second = ins2;
            }
        }
    }
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    total_gate_time += duration;
    if (gateLog) std::cout << "X" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Y(int t) {
    #ifdef TO_QASM
        system(("echo 'y qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    X(t); gateCount--;
    Diagonal_Gate(t, std::bind(&Symbol::degree90cw, std::placeholders::_1), std::bind(&Symbol::omega_multiplication, std::placeholders::_1, 2));
    // remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    total_gate_time += duration;
    if (gateLog) std::cout << "Y" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Z(int t, bool opt) {
    #ifdef TO_QASM
        system(("echo 'z qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    Diagonal_Gate(t, [](Symbol*) {}, std::bind(&Symbol::negate, std::placeholders::_1));
    if (opt) {
        // remove_useless();
        reduce();
    }
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    total_gate_time += duration;
    if (gateLog) std::cout << "Z" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::H(int t) {
    #ifdef TO_QASM
        system(("echo 'h qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    General_Single_Qubit_Gate(t,
        [](const Symbol &l, const Symbol &r) -> Symbol { return (l + r).divide_by_the_square_root_of_two(); },
        [](const Symbol &l, const Symbol &r) -> Symbol { return (l - r).divide_by_the_square_root_of_two(); });
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "H" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::S(int t) {
    #ifdef TO_QASM
        system(("echo 's qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    Diagonal_Gate(t, [](Symbol*) {}, std::bind(&Symbol::omega_multiplication, std::placeholders::_1, 2));
    // remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "S" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::T(int t) {
    #ifdef TO_QASM
        system(("echo 't qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    Diagonal_Gate(t, [](Symbol*) {}, std::bind(&Symbol::omega_multiplication, std::placeholders::_1, 1));
    // remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "T" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Rx(const boost::rational<boost::multiprecision::cpp_int> &theta, int t) {
    #ifdef TO_QASM
        system(("echo 'rx(...) qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    General_Single_Qubit_Gate(t,
        [theta](Symbol l, Symbol r) -> Symbol { return l.multiply_cos(theta/2) - r.multiply_isin(theta/2); },
        [theta](Symbol l, Symbol r) -> Symbol { return r.multiply_cos(theta/2) - l.multiply_isin(theta/2); });
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "Rx" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Ry(int t) {
    #ifdef TO_QASM
        system(("echo 'ry(pi/2) qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    General_Single_Qubit_Gate(t,
        [](const Symbol &l, const Symbol &r) -> Symbol { return (l - r).divide_by_the_square_root_of_two(); },
        [](const Symbol &l, const Symbol &r) -> Symbol { return (l + r).divide_by_the_square_root_of_two(); });
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "Ry" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

// https://quantumcomputinguk.org/tutorials/introduction-to-the-rz-gate-with-code
template <typename Symbol>
void AUTOQ::Automata<Symbol>::Rz(const boost::rational<boost::multiprecision::cpp_int> &theta, int t) {
    #ifdef TO_QASM
        system(("echo 'rz(...) qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    // General_Single_Qubit_Gate(t,
    //     [theta](Symbol l, const Symbol &r) -> Symbol { return l.counterclockwise(-theta / 2); },
    //     [theta](const Symbol &l, Symbol r) -> Symbol { return r.counterclockwise(theta / 2); });
    Diagonal_Gate(t, std::bind(&Symbol::counterclockwise, std::placeholders::_1, -theta / 2), std::bind(&Symbol::counterclockwise, std::placeholders::_1, theta / 2));
    // remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    total_gate_time += duration;
    if (gateLog) std::cout << "Rz" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::Convert::toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::CX(int c, int t, bool opt) {
    #ifdef TO_QASM
        system(("echo 'cx qubits[" + std::to_string(c-1) + "], qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    assert(c != t);
    if (c > t) {
        General_Controlled_Gate(c, t,
            [](const Symbol &, const Symbol &r) -> Symbol { return r; },
            [](const Symbol &l, const Symbol &) -> Symbol { return l; });
    } else {
        TopDownTransitions transitions2;
        std::map<State, int> topStateIsLeftOrRight, childStateIsLeftOrRight; // 0b10: original tree, 0b01: copied tree, 0b11: both trees
        // std::map<State, State> topStateMap, childStateMap;
        // If a state has only one tree, then its id does not change. In this case, it is not present in this map.
        // If a state has two trees, then it presents in this map and its value is the id in the copied tree.

        // Convert from TopDownTransitions to InternalTopDownTransitions.
        InternalTopDownTransitions internalTransitions(qubitNum + 1); // only contains qubits from c to the bottom
        TopDownTransitions leafTransitions;
        for (const auto &tr : transitions) {
            if (tr.first.is_internal()) {
                if (tr.first.symbol().qubit() < c)
                    transitions2[tr.first] = tr.second;
                else
                    internalTransitions[static_cast<int>(tr.first.symbol().qubit())][tr.first.tag()] = tr.second;
            } else {
                leafTransitions[tr.first] = tr.second;
            }
        }

        // Assume the initial state numbers are already compact.
        for (int q = c; q <= qubitNum; q++) {
            if (q == c) {
                /* Construct childStateIsLeftOrRight. */
                for (const auto &tag_outins : internalTransitions[q]) {
                    for (const auto &out_ins : tag_outins.second) {
                        for (const auto &in : out_ins.second) {
                            assert(in.size() == 2);
                            childStateIsLeftOrRight[in[0]] |= 0b10;
                            childStateIsLeftOrRight[in[1]] |= 0b01;
                        }
                    }
                }
                /**************************************/
                /* Construct childStateMap. */
                // for (const auto &kv : childStateIsLeftOrRight) {
                //     if (kv.second == 0b11) {
                //         childStateMap[kv.first] = stateNum;
                //         stateNum++;
                //     }
                // }
                /****************************/
                for (const auto &tag_outins : internalTransitions[q]) {
                    auto &ref = transitions2[{Symbol(q), tag_outins.first}];
                    for (const auto &out_ins : tag_outins.second) {
                        const auto &top = out_ins.first;
                        auto &reftop = ref[top];
                        for (const auto &in : out_ins.second) {
                            assert(in.size() == 2);
                            queryChildID(in[1], newIn1);
                            reftop.insert({in[0], newIn1});
                        }
                    }
                }
            } else { // if (q > c) {
                /* Construct childStateIsLeftOrRight. */
                for (const auto &tag_outins : internalTransitions[q]) {
                    for (const auto &out_ins : tag_outins.second) {
                        const auto &top = out_ins.first;
                        auto val = topStateIsLeftOrRight[top];
                        for (const auto &in : out_ins.second) {
                            assert(in.size() == 2);
                            childStateIsLeftOrRight[in[0]] |= val;
                            childStateIsLeftOrRight[in[1]] |= val;
                        }
                    }
                }
                /**************************************/
                /* Construct childStateMap. */
                // for (const auto &kv : childStateIsLeftOrRight) {
                //     if (kv.second == 0b11) {
                //         childStateMap[kv.first] = stateNum;
                //         stateNum++;
                //     }
                // }
                /****************************/
                for (const auto &tag_outins : internalTransitions[q]) {
                    auto &ref = transitions2[{Symbol(q), tag_outins.first}];
                    for (const auto &out_ins : tag_outins.second) {
                        const auto &top = out_ins.first;
                        auto val = topStateIsLeftOrRight[top];
                        if (val & 0b10) {
                            ref[top] = out_ins.second;
                        }
                        if (val & 0b01) {
                            queryTopID(top, newTop);
                            auto &refnewTop = ref[newTop];
                            for (const auto &in : out_ins.second) {
                                assert(in.size() == 2);
                                queryChildID(in[0], newIn0);
                                queryChildID(in[1], newIn1);
                                if (q == t) {
                                    refnewTop.insert({newIn1, newIn0});
                                } else {
                                    refnewTop.insert({newIn0, newIn1});
                                }
                            }
                        }
                    }
                }
            }
            /**********************************************/
            topStateIsLeftOrRight = childStateIsLeftOrRight;
            childStateIsLeftOrRight.clear();
            // topStateMap = childStateMap;
            // childStateMap.clear();
            /**********************************************/
        }
        for (const auto &tr : leafTransitions) {
            auto &ref = transitions2[tr.first];
            for (const auto &out_ins : tr.second) {
                const auto &top = out_ins.first;
                auto val = topStateIsLeftOrRight[top];
                if (val & 0b10) {
                    ref[top].insert({{}});
                }
                if (val & 0b01) {
                    queryTopID(top, newTop);
                    ref[newTop].insert({{}});
                }
            }
        }
        transitions = transitions2;
        stateNum *= 2;
    }
    if (opt) {
        // remove_useless();
        reduce();
    }
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    total_gate_time += duration;
    if (gateLog) std::cout << "CX" << c << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

#define queryTopID2(oldID, newID) \
    State newID = oldID + stateNum * 2;/*
    // {   \
    //     auto it = topStateMap2.find(oldID);    \
    //     if (it == topStateMap2.end()) {   \
    //         it = topStateMap.find(oldID);  \
    //         if (it == topStateMap.end()) {    \
    //             newID = oldID;    \
    //         } else { \
    //             newID = it->second; \
    //         }   \
    //     } else {   \
    //         newID = it->second; \
    //     }   \
    // }*/
#define queryChildID2(oldID, newID) \
    State newID = oldID + stateNum * 2;/*
    // {   \
    //     auto it = childStateMap2.find(oldID);    \
    //     if (it == childStateMap2.end()) {   \
    //         it = childStateMap.find(oldID);  \
    //         if (it == childStateMap.end()) {    \
    //             newID = oldID;    \
    //         } else { \
    //             newID = it->second; \
    //         }   \
    //     } else {   \
    //         newID = it->second; \
    //     }   \
    // }*/
template <typename Symbol>
void AUTOQ::Automata<Symbol>::CZ(int c, int t) {
    #ifdef TO_QASM
        system(("echo 'cz qubits[" + std::to_string(c-1) + "], qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    assert(c != t);
    if (c > t) std::swap(c, t);
    auto start = std::chrono::steady_clock::now();
    TopDownTransitions transitions2;
    std::map<State, int> topStateIsLeftOrRight, childStateIsLeftOrRight; // 0b10: original tree, 0b01: copied tree, 0b11: both trees
    // std::map<State, State> topStateMap, childStateMap;
    std::map<State, int> topStateIsLeftOrRight2, childStateIsLeftOrRight2; // 0b10: original tree, 0b01: copied tree, 0b11: both trees
    // std::map<State, State> topStateMap2, childStateMap2;
    // If a state has only one tree, then its id does not change. In this case, it is not present in this map.
    // If a state has two trees, then it presents in this map and its value is the id in the copied tree.

    // Convert from TopDownTransitions to InternalTopDownTransitions.
    InternalTopDownTransitions internalTransitions(qubitNum + 1); // only contains qubits from c to the bottom
    TopDownTransitions leafTransitions;
    for (const auto &tr : transitions) {
        if (tr.first.is_internal()) {
            if (tr.first.symbol().qubit() < c)
                transitions2[tr.first] = tr.second;
            else
                internalTransitions[static_cast<int>(tr.first.symbol().qubit())][tr.first.tag()] = tr.second;
        } else {
            leafTransitions[tr.first] = tr.second;
        }
    }

    // Assume the initial state numbers are already compact.
    for (int q = c; q <= qubitNum; q++) {
        if (q == c) {
            /* Construct childStateIsLeftOrRight. */
            for (const auto &tag_outins : internalTransitions[q]) {
                for (const auto &out_ins : tag_outins.second) {
                    for (const auto &in : out_ins.second) {
                        assert(in.size() == 2);
                        childStateIsLeftOrRight[in[0]] |= 0b10;
                        childStateIsLeftOrRight[in[1]] |= 0b01;
                    }
                }
            }
            /**************************************/
            /* Construct childStateMap. */
            // for (const auto &kv : childStateIsLeftOrRight) {
            //     if (kv.second == 0b11) {
            //         childStateMap[kv.first] = stateNum;
            //         stateNum++;
            //     }
            // }
            /****************************/
            for (const auto &tag_outins : internalTransitions[q]) {
                auto &ref = transitions2[{Symbol(q), tag_outins.first}];
                for (const auto &out_ins : tag_outins.second) {
                    const auto &top = out_ins.first;
                    auto &reftop = ref[top];
                    for (const auto &in : out_ins.second) {
                        assert(in.size() == 2);
                        queryChildID(in[1], newIn1);
                        reftop.insert({in[0], newIn1});
                    }
                }
            }
        } else if (q < t) { // if (c < q < t) {
            /* Construct childStateIsLeftOrRight. */
            for (const auto &tag_outins : internalTransitions[q]) {
                for (const auto &out_ins : tag_outins.second) {
                    const auto &top = out_ins.first;
                    auto val = topStateIsLeftOrRight[top];
                    for (const auto &in : out_ins.second) {
                        assert(in.size() == 2);
                        childStateIsLeftOrRight[in[0]] |= val;
                        childStateIsLeftOrRight[in[1]] |= val;
                    }
                }
            }
            /**************************************/
            /* Construct childStateMap. */
            // for (const auto &kv : childStateIsLeftOrRight) {
            //     if (kv.second == 0b11) {
            //         childStateMap[kv.first] = stateNum;
            //         stateNum++;
            //     }
            // }
            /****************************/
            for (const auto &tag_outins : internalTransitions[q]) {
                auto &ref = transitions2[{Symbol(q), tag_outins.first}];
                for (const auto &out_ins : tag_outins.second) {
                    const auto &top = out_ins.first;
                    auto val = topStateIsLeftOrRight[top];
                    if (val & 0b10) {
                        ref[top] = out_ins.second;
                    }
                    if (val & 0b01) {
                        queryTopID(top, newTop);
                        auto &refnewTop = ref[newTop];
                        for (const auto &in : out_ins.second) {
                            assert(in.size() == 2);
                            queryChildID(in[0], newIn0);
                            queryChildID(in[1], newIn1);
                            refnewTop.insert({newIn0, newIn1});
                        }
                    }
                }
            }
        } else if (q == t) {
            /* Construct childStateIsLeftOrRight. */
            for (const auto &tag_outins : internalTransitions[q]) {
                for (const auto &out_ins : tag_outins.second) {
                    const auto &top = out_ins.first;
                    auto val = topStateIsLeftOrRight[top];
                    for (const auto &in : out_ins.second) {
                        assert(in.size() == 2);
                        childStateIsLeftOrRight[in[0]] |= val;
                        childStateIsLeftOrRight[in[1]] |= val;
                        if (val & 0b01) {
                            childStateIsLeftOrRight2[in[0]] |= 0b10;
                            childStateIsLeftOrRight2[in[1]] |= 0b01;
                        }
                    }
                }
            }
            /**************************************/
            /* Construct childStateMap. */
            // for (const auto &kv : childStateIsLeftOrRight) {
            //     if (kv.second == 0b11) {
            //         childStateMap[kv.first] = stateNum;
            //         stateNum++;
            //     }
            // }
            // for (const auto &kv : childStateIsLeftOrRight2) {
            //     if (kv.second == 0b11) {
            //         childStateMap2[kv.first] = stateNum;
            //         stateNum++;
            //     }
            // }
            /****************************/
            for (const auto &tag_outins : internalTransitions[q]) {
                auto &ref = transitions2[{Symbol(q), tag_outins.first}];
                for (const auto &out_ins : tag_outins.second) {
                    const auto &top = out_ins.first;
                    auto val = topStateIsLeftOrRight[top];
                    if (val & 0b10) {
                        ref[top] = out_ins.second;
                    }
                    if (val & 0b01) {
                        queryTopID(top, newTop);
                        auto &refnewTop = ref[newTop];
                        for (const auto &in : out_ins.second) {
                            assert(in.size() == 2);
                            queryChildID(in[0], newIn0);
                            queryChildID2(in[1], newIN1);
                            refnewTop.insert({newIn0, newIN1});
                        }
                    }
                }
            }
        } else { // if (q > t) {
            /* Construct childStateIsLeftOrRight. */
            for (const auto &tag_outins : internalTransitions[q]) {
                for (const auto &out_ins : tag_outins.second) {
                    const auto &top = out_ins.first;
                    auto val = topStateIsLeftOrRight[top];
                    auto val2 = topStateIsLeftOrRight2[top];
                    for (const auto &in : out_ins.second) {
                        assert(in.size() == 2);
                        childStateIsLeftOrRight[in[0]] |= val;
                        childStateIsLeftOrRight[in[1]] |= val;
                        childStateIsLeftOrRight2[in[0]] |= val2;
                        childStateIsLeftOrRight2[in[1]] |= val2;
                    }
                }
            }
            /**************************************/
            /* Construct childStateMap. */
            // for (const auto &kv : childStateIsLeftOrRight) {
            //     if (kv.second == 0b11) {
            //         childStateMap[kv.first] = stateNum;
            //         stateNum++;
            //     }
            // }
            // for (const auto &kv : childStateIsLeftOrRight2) {
            //     if (kv.second == 0b11) {
            //         childStateMap2[kv.first] = stateNum;
            //         stateNum++;
            //     }
            // }
            /****************************/
            for (const auto &tag_outins : internalTransitions[q]) {
                auto &ref = transitions2[{Symbol(q), tag_outins.first}];
                for (const auto &out_ins : tag_outins.second) {
                    const auto &top = out_ins.first;
                    auto val = topStateIsLeftOrRight[top];
                    if (val & 0b10) {
                        ref[top] = out_ins.second;
                    }
                    if (val & 0b01) {
                        auto val2 = topStateIsLeftOrRight2[top];
                        if (val2 & 0b10) {
                            queryTopID(top, newTop);
                            auto &refnewTop = ref[newTop];
                            for (const auto &in : out_ins.second) {
                                assert(in.size() == 2);
                                queryChildID(in[0], newIn0);
                                queryChildID(in[1], newIn1);
                                refnewTop.insert({newIn0, newIn1});
                            }
                        }
                        if (val2 & 0b01) {
                            queryTopID2(top, newTop);
                            auto &refnewTop = ref[newTop];
                            for (const auto &in : out_ins.second) {
                                assert(in.size() == 2);
                                queryChildID2(in[0], newIn0);
                                queryChildID2(in[1], newIn1);
                                refnewTop.insert({newIn0, newIn1});
                            }
                        }
                    }
                }
            }
        }
        /**********************************************/
        topStateIsLeftOrRight = childStateIsLeftOrRight;
        childStateIsLeftOrRight.clear();
        // topStateMap = childStateMap;
        // childStateMap.clear();
        topStateIsLeftOrRight2 = childStateIsLeftOrRight2;
        childStateIsLeftOrRight2.clear();
        // topStateMap2 = childStateMap2;
        // childStateMap2.clear();
        /**********************************************/
    }
    for (const auto &tr : leafTransitions) {
        auto &ref = transitions2[tr.first];
        for (const auto &out_ins : tr.second) {
            const auto &top = out_ins.first;
            auto val = topStateIsLeftOrRight[top];
            if (val & 0b10) {
                ref[top].insert({{}});
            }
            if (val & 0b01) {
                auto val2 = topStateIsLeftOrRight2[top];
                if (val2 & 0b10) {
                    queryTopID(top, newTop);
                    ref[newTop].insert({{}});
                }
                if (val2 & 0b01) {
                    queryTopID2(top, newTop);
                    SymbolTag symbol_tag = tr.first;
                    symbol_tag.symbol().negate();
                    transitions2[symbol_tag][newTop].insert({{}});
                }
            }
        }
    }
    transitions = transitions2;
    stateNum *= 3;
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    total_gate_time += duration;
    if (gateLog) std::cout << "CZ" << c << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::CCX(int c, int c2, int t) {
    #ifdef TO_QASM
        system(("echo 'ccx qubits[" + std::to_string(c-1) + "], qubits[" + std::to_string(c2-1) + "], qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    assert(c != c2 && c2 != t && t != c);
    if (c > c2) std::swap(c, c2); // ensure c < c2
    if (c2 < t) { // c < c2 < t
        TopDownTransitions transitions2;
        std::map<State, int> topStateIsLeftOrRight, childStateIsLeftOrRight; // 0b10: original tree, 0b01: copied tree, 0b11: both trees
        // std::map<State, State> topStateMap, childStateMap;
        std::map<State, int> topStateIsLeftOrRight2, childStateIsLeftOrRight2; // 0b10: original tree, 0b01: copied tree, 0b11: both trees
        // std::map<State, State> topStateMap2, childStateMap2;
        // If a state has only one tree, then its id does not change. In this case, it is not present in this map.
        // If a state has two trees, then it presents in this map and its value is the id in the copied tree.

        // Convert from TopDownTransitions to InternalTopDownTransitions.
        InternalTopDownTransitions internalTransitions(qubitNum + 1); // only contains qubits from c to the bottom
        TopDownTransitions leafTransitions;
        for (const auto &tr : transitions) {
            if (tr.first.is_internal()) {
                if (tr.first.symbol().qubit() < c)
                    transitions2[tr.first] = tr.second;
                else
                    internalTransitions[static_cast<int>(tr.first.symbol().qubit())][tr.first.tag()] = tr.second;
            } else {
                leafTransitions[tr.first] = tr.second;
            }
        }

        // Assume the initial state numbers are already compact.
        for (int q = c; q <= qubitNum; q++) {
            if (q == c) {
                /* Construct childStateIsLeftOrRight. */
                for (const auto &tag_outins : internalTransitions[q]) {
                    for (const auto &out_ins : tag_outins.second) {
                        for (const auto &in : out_ins.second) {
                            assert(in.size() == 2);
                            childStateIsLeftOrRight[in[0]] |= 0b10;
                            childStateIsLeftOrRight[in[1]] |= 0b01;
                        }
                    }
                }
                /**************************************/
                /* Construct childStateMap. */
                // for (const auto &kv : childStateIsLeftOrRight) {
                //     if (kv.second == 0b11) {
                //         childStateMap[kv.first] = stateNum;
                //         stateNum++;
                //     }
                // }
                /****************************/
                for (const auto &tag_outins : internalTransitions[q]) {
                    auto &ref = transitions2[{Symbol(q), tag_outins.first}];
                    for (const auto &out_ins : tag_outins.second) {
                        const auto &top = out_ins.first;
                        auto &reftop = ref[top];
                        for (const auto &in : out_ins.second) {
                            assert(in.size() == 2);
                            queryChildID(in[1], newIn1);
                            reftop.insert({in[0], newIn1});
                        }
                    }
                }
            } else if (q < c2) { // if (c < q < c2) {
                /* Construct childStateIsLeftOrRight. */
                for (const auto &tag_outins : internalTransitions[q]) {
                    for (const auto &out_ins : tag_outins.second) {
                        const auto &top = out_ins.first;
                        auto val = topStateIsLeftOrRight[top];
                        for (const auto &in : out_ins.second) {
                            assert(in.size() == 2);
                            childStateIsLeftOrRight[in[0]] |= val;
                            childStateIsLeftOrRight[in[1]] |= val;
                        }
                    }
                }
                /**************************************/
                /* Construct childStateMap. */
                // for (const auto &kv : childStateIsLeftOrRight) {
                //     if (kv.second == 0b11) {
                //         childStateMap[kv.first] = stateNum;
                //         stateNum++;
                //     }
                // }
                /****************************/
                for (const auto &tag_outins : internalTransitions[q]) {
                    auto &ref = transitions2[{Symbol(q), tag_outins.first}];
                    for (const auto &out_ins : tag_outins.second) {
                        const auto &top = out_ins.first;
                        auto val = topStateIsLeftOrRight[top];
                        if (val & 0b10) {
                            ref[top] = out_ins.second;
                        }
                        if (val & 0b01) {
                            queryTopID(top, newTop);
                            auto &refnewTop = ref[newTop];
                            for (const auto &in : out_ins.second) {
                                assert(in.size() == 2);
                                queryChildID(in[0], newIn0);
                                queryChildID(in[1], newIn1);
                                refnewTop.insert({newIn0, newIn1});
                            }
                        }
                    }
                }
            } else if (q == c2) {
                /* Construct childStateIsLeftOrRight. */
                for (const auto &tag_outins : internalTransitions[q]) {
                    for (const auto &out_ins : tag_outins.second) {
                        const auto &top = out_ins.first;
                        auto val = topStateIsLeftOrRight[top];
                        for (const auto &in : out_ins.second) {
                            assert(in.size() == 2);
                            childStateIsLeftOrRight[in[0]] |= val;
                            childStateIsLeftOrRight[in[1]] |= val;
                            if (val & 0b01) {
                                childStateIsLeftOrRight2[in[0]] |= 0b10;
                                childStateIsLeftOrRight2[in[1]] |= 0b01;
                            }
                        }
                    }
                }
                /**************************************/
                /* Construct childStateMap. */
                // for (const auto &kv : childStateIsLeftOrRight) {
                //     if (kv.second == 0b11) {
                //         childStateMap[kv.first] = stateNum;
                //         stateNum++;
                //     }
                // }
                // for (const auto &kv : childStateIsLeftOrRight2) {
                //     if (kv.second == 0b11) {
                //         childStateMap2[kv.first] = stateNum;
                //         stateNum++;
                //     }
                // }
                /****************************/
                for (const auto &tag_outins : internalTransitions[q]) {
                    auto &ref = transitions2[{Symbol(q), tag_outins.first}];
                    for (const auto &out_ins : tag_outins.second) {
                        const auto &top = out_ins.first;
                        auto val = topStateIsLeftOrRight[top];
                        if (val & 0b10) {
                            ref[top] = out_ins.second;
                        }
                        if (val & 0b01) {
                            queryTopID(top, newTop);
                            auto &refnewTop = ref[newTop];
                            for (const auto &in : out_ins.second) {
                                assert(in.size() == 2);
                                queryChildID(in[0], newIn0);
                                queryChildID2(in[1], newIN1);
                                refnewTop.insert({newIn0, newIN1});
                            }
                        }
                    }
                }
            } else { // if (q > c2) {
                /* Construct childStateIsLeftOrRight. */
                for (const auto &tag_outins : internalTransitions[q]) {
                    for (const auto &out_ins : tag_outins.second) {
                        const auto &top = out_ins.first;
                        auto val = topStateIsLeftOrRight[top];
                        auto val2 = topStateIsLeftOrRight2[top];
                        for (const auto &in : out_ins.second) {
                            assert(in.size() == 2);
                            childStateIsLeftOrRight[in[0]] |= val;
                            childStateIsLeftOrRight[in[1]] |= val;
                            childStateIsLeftOrRight2[in[0]] |= val2;
                            childStateIsLeftOrRight2[in[1]] |= val2;
                        }
                    }
                }
                /**************************************/
                /* Construct childStateMap. */
                // for (const auto &kv : childStateIsLeftOrRight) {
                //     if (kv.second == 0b11) {
                //         childStateMap[kv.first] = stateNum;
                //         stateNum++;
                //     }
                // }
                // for (const auto &kv : childStateIsLeftOrRight2) {
                //     if (kv.second == 0b11) {
                //         childStateMap2[kv.first] = stateNum;
                //         stateNum++;
                //     }
                // }
                /****************************/
                for (const auto &tag_outins : internalTransitions[q]) {
                    auto &ref = transitions2[{Symbol(q), tag_outins.first}];
                    for (const auto &out_ins : tag_outins.second) {
                        const auto &top = out_ins.first;
                        auto val = topStateIsLeftOrRight[top];
                        if (val & 0b10) {
                            ref[top] = out_ins.second;
                        }
                        if (val & 0b01) {
                            auto val2 = topStateIsLeftOrRight2[top];
                            if (val2 & 0b10) {
                                queryTopID(top, newTop);
                                auto &refnewTop = ref[newTop];
                                for (const auto &in : out_ins.second) {
                                    assert(in.size() == 2);
                                    queryChildID(in[0], newIn0);
                                    queryChildID(in[1], newIn1);
                                    refnewTop.insert({newIn0, newIn1});
                                }
                            }
                            if (val2 & 0b01) {
                                queryTopID2(top, newTop);
                                auto &refnewTop = ref[newTop];
                                for (const auto &in : out_ins.second) {
                                    assert(in.size() == 2);
                                    queryChildID2(in[0], newIn0);
                                    queryChildID2(in[1], newIn1);
                                    if (q == t)
                                        refnewTop.insert({newIn1, newIn0});
                                    else
                                        refnewTop.insert({newIn0, newIn1});
                                }
                            }
                        }
                    }
                }
            }
            /**********************************************/
            topStateIsLeftOrRight = childStateIsLeftOrRight;
            childStateIsLeftOrRight.clear();
            // topStateMap = childStateMap;
            // childStateMap.clear();
            topStateIsLeftOrRight2 = childStateIsLeftOrRight2;
            childStateIsLeftOrRight2.clear();
            // topStateMap2 = childStateMap2;
            // childStateMap2.clear();
            /**********************************************/
        }
        for (const auto &tr : leafTransitions) {
            const auto &symbol_tag = tr.first;
            auto &ref = transitions2[symbol_tag];
            for (const auto &out_ins : tr.second) {
                const auto &top = out_ins.first;
                auto val = topStateIsLeftOrRight[top];
                if (val & 0b10) {
                    ref[top].insert({{}});
                }
                if (val & 0b01) {
                    auto val2 = topStateIsLeftOrRight2[top];
                    if (val2 & 0b10) {
                        queryTopID(top, newTop);
                        ref[newTop].insert({{}});
                    }
                    if (val2 & 0b01) {
                        queryTopID2(top, newTop2);
                        ref[newTop2].insert({{}});
                    }
                }
            }
        }
        transitions = transitions2;
        stateNum *= 3;
    } else if (t < c) { // t < c < c2
        General_Controlled_Gate(c, c2, t,
            [](const Symbol &, const Symbol &r) -> Symbol { return r; },
            [](const Symbol &l, const Symbol &) -> Symbol { return l; });
    } else { // c < t < c2
        auto aut2 = *this;
        aut2.CX(c2, t, false); gateCount--; // prevent repeated counting
        for (const auto &tr : aut2.transitions) {
            const SymbolTag &symbol_tag = tr.first;
            if (!(symbol_tag.is_internal() && symbol_tag.symbol().qubit() <= c)) {
                auto &ttf = transitions[symbol_tag];
                for (const auto &out_ins : tr.second) {
                    const auto &q = out_ins.first + stateNum;
                    for (auto in : out_ins.second) {
                        for (unsigned i=0; i<in.size(); i++)
                            in.at(i) += stateNum;
                        ttf[q].insert(in);
                    }
                }
            }
        }
        for (auto &tr : transitions) {
            if (tr.first.is_leaf() || (tr.first.is_internal() && tr.first.symbol().qubit() > c)) break;
            if (tr.first.is_internal() && tr.first.symbol().qubit() == c) {
                for (auto &out_ins : tr.second) {
                    std::vector<StateVector> vec(out_ins.second.begin(), out_ins.second.end());
                    for (auto &in : vec) {
                        assert(in.size() == 2);
                        if (in.at(0) < stateNum && in.at(1) < stateNum) {
                            in.at(1) += stateNum;
                        }
                    }
                    out_ins.second = std::set<StateVector>(vec.begin(), vec.end());
                }
            }
        }
        stateNum += aut2.stateNum;
        remove_useless();
    }
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    total_gate_time += duration;
    if (gateLog) std::cout << "CCX" << c << "," << c2 << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Tdg(int t) {
    // #ifdef TO_QASM
    //     system(("echo 'tdg qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
    //     return;
    // #endif
    auto start = std::chrono::steady_clock::now();
    Diagonal_Gate(t, [](Symbol*) {}, std::bind(&Symbol::degree45cw, std::placeholders::_1));
    // remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    total_gate_time += duration;
    if (gateLog) std::cout << "Tdg" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Sdg(int t) {
    // #ifdef TO_QASM
    //     system(("echo 'sdg qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
    //     return;
    // #endif
    auto start = std::chrono::steady_clock::now();
    Diagonal_Gate(t, [](Symbol*) {}, std::bind(&Symbol::degree90cw, std::placeholders::_1));
    // remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    total_gate_time += duration;
    if (gateLog) std::cout << "Sdg" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Swap(int t1, int t2) {
    // #ifdef TO_QASM
    //     system(("echo 'swap qubits[" + std::to_string(t1-1) + "], qubits[" + std::to_string(t2-1) + "];' >> " + QASM_FILENAME).c_str());
    //     return;
    // #endif
    auto start = std::chrono::steady_clock::now();
    CX(t1, t2); gateCount--; // prevent repeated counting
    CX(t2, t1); gateCount--; // prevent repeated counting
    CX(t1, t2); gateCount--; // prevent repeated counting
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    // total_gate_time += 0;
    if (gateLog) std::cout << "swap" << t1 << "," << t2 << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::CX() {
    // auto start = std::chrono::steady_clock::now();
    TopDownTransitions transitions_result;
    for (const auto &fc_ois : transitions) {
        const auto &fc = fc_ois.first;
        const auto &ois = fc_ois.second;
        auto &transitions_result_fc = transitions_result[fc];
        // auto &transitions_result_fc2 = transitions_result_fc[top + stateNum]
        if (fc.first.is_leaf()) {
            for (const auto &oi : ois) {
                const auto &top = oi.first;
                const auto &ins = oi.second;
                transitions_result_fc[top].insert(ins.begin(), ins.end());
                transitions_result_fc[top + stateNum].insert(ins.begin(), ins.end());
            }
        } else {
            for (const auto &oi : ois) {
                const auto &top = oi.first;
                const auto &ins = oi.second;
                auto &ref = transitions_result_fc[top];
                auto &ref2 = transitions_result_fc[top + stateNum];
                for (const auto &in : ins) {
                    ref.insert({in.at(0), in.at(1) + stateNum});
                    ref2.insert({in.at(1), in.at(0) + stateNum});
                }
            }
        }
    }
    transitions = transitions_result;
    stateNum *= 2;
    remove_useless();
    reduce();
    gateCount++;
    // auto duration = std::chrono::steady_clock::now() - start;
    // if (gateLog) std::cout << "CNOT" << c << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::CX_inv() {
    // auto start = std::chrono::steady_clock::now();
    TopDownTransitions transitions_result;
    for (const auto &fc_ois : transitions) {
        const auto &fc = fc_ois.first;
        const auto &ois = fc_ois.second;
        auto &transitions_result_fc = transitions_result[fc];
        // auto &transitions_result_fc2 = transitions_result_fc[top + stateNum]
        if (fc.first.is_leaf()) {
            for (const auto &oi : ois) {
                const auto &top = oi.first;
                const auto &ins = oi.second;
                transitions_result_fc[top].insert(ins.begin(), ins.end());
                transitions_result_fc[top + stateNum].insert(ins.begin(), ins.end());
            }
        } else {
            for (const auto &oi : ois) {
                const auto &top = oi.first;
                const auto &ins = oi.second;
                auto &ref = transitions_result_fc[top];
                auto &ref2 = transitions_result_fc[top + stateNum];
                for (const auto &in : ins) {
                    ref.insert({in.at(0), in.at(1) + stateNum});
                    ref2.insert({in.at(1) + stateNum, in.at(0)});
                }
            }
        }
    }
    transitions = transitions_result;
    stateNum *= 2;
    remove_useless();
    reduce();
    gateCount++;
    // auto duration = std::chrono::steady_clock::now() - start;
    // if (gateLog) std::cout << "CNOT" << c << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::Convert::toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Phase(const boost::rational<boost::multiprecision::cpp_int> &r) {
    // auto start = std::chrono::steady_clock::now();
    TopDownTransitions transitions_result;
    for (const auto &fc_ois : transitions) {
        auto symbol = fc_ois.first.symbol();
        const auto &tag = fc_ois.first.tag();
        if (symbol.is_internal())
            transitions_result.insert(fc_ois);
        else
            transitions_result[{symbol.counterclockwise(r), tag}] = fc_ois.second;
    }
    transitions = transitions_result;
    gateCount++;
    // auto duration = std::chrono::steady_clock::now() - start;
    // if (gateLog) std::cout << "Phase" << c << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::Convert::toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::randG(int G, int A, int B, int C) {
    int g, a, b=0, c=0;
    do {
        g = rand() % 11;
        a = rand() % qubitNum + 1;
        if (g >= 8) {
            do {
                b = rand() % qubitNum + 1;
            } while (b == a);
        }
        if (g >= 10) {
            do {
                c = rand() % qubitNum + 1;
            } while (c == a || c == b);
        }
    } while (g==G && a==A && (g<8 || G<8 || b==B) && (g<10 || G<10 || c==C));
    switch(g) {
        case 0: X(a); break;
        case 1: Y(a); break;
        case 2: Z(a); break;
        case 3: H(a); break;
        case 4: S(a); break;
        case 5: T(a); break;
        case 6: Rx(boost::rational<boost::multiprecision::cpp_int>(1, 4), a); break;
        case 7: Ry(a); break;
        case 8: CX(a, b); break;
        case 9: CZ(a, b); break;
        case 10: CCX(a, b, c); break;
        // case 11: Fredkin(a, b, c); break;
        default: break;
    }
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
