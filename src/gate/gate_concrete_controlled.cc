/** Concrete controlled gates: CX, CZ, CCX. */
#include "autoq/aut_description.hh"
#include "autoq/util/util.hh"
#include "autoq/gate_macros.hh"
#include <boost/rational.hpp>
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wold-style-cast"
#include <boost/multiprecision/cpp_int.hpp>
#pragma GCC diagnostic pop


// --- Concrete controlled: CX, CZ, CCX ---
template <typename Symbol>
void AUTOQ::Automata<Symbol>::CX(int c, int t, bool opt) {
    #ifdef TO_QASM
        system(("echo 'cx qubits[" + std::to_string(c-1) + "], qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    assert(c != t);
    if (c > t) {
        general_controlled_gate(c, t,
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
    stats_->gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    stats_->total_gate_time += duration;
    if (stats_->gateLog) std::cout << "CX" << c << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}
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
    stats_->gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    stats_->total_gate_time += duration;
    if (stats_->gateLog) std::cout << "CZ" << c << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
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
        general_controlled_gate(c, c2, t,
            [](const Symbol &, const Symbol &r) -> Symbol { return r; },
            [](const Symbol &l, const Symbol &) -> Symbol { return l; });
    } else { // c < t < c2
        auto aut2 = *this;
        aut2.CX(c2, t, false); stats_->gateCount--; // prevent repeated counting
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
    stats_->gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    stats_->total_gate_time += duration;
    if (stats_->gateLog) std::cout << "CCX" << c << "," << c2 << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
