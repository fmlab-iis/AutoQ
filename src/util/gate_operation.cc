#include <functional>
#include <boost/rational.hpp>
#include <autoq/aut_description.hh>
#include <boost/multiprecision/cpp_int.hpp>

// #define TO_QASM
#define QASM_FILENAME "circuit.qasm"
// OPENQASM 2.0;
// include "qelib1.inc";
// qreg qubits[?];

namespace {
    std::string toString(std::chrono::steady_clock::duration tp) {
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
            ss << d.count() << 'd' << h.count() << 'h' << m.count() << 'm' << s.count() << 's';
        else if (m.count() == 0 && s.count() < 10) {
            ss << s.count() << '.' << ms.count() / 100 << "s";
        } else {
            if (m.count() > 0) ss << m.count() << 'm';
            ss << s.count() << 's';// << " & ";
        }
        ss.fill(fill);
        return ss.str();
    }
}

#define queryTopID(oldID, newID) \
    State newID;    \
    {   \
        auto it = topStateMap.find(oldID);    \
        if (it == topStateMap.end())    \
            newID = oldID;    \
        else    \
            newID = it->second; \
    }
#define queryChildID(oldID, newID) \
    State newID;    \
    {   \
        auto it = childStateMap.find(oldID);    \
        if (it == childStateMap.end())    \
            newID = oldID;    \
        else    \
            newID = it->second; \
    }
template <typename Symbol>
void AUTOQ::Automata<Symbol>::diagonal_gate(int t, const std::function<void(Symbol*)> &multiply_by_c0, const std::function<void(Symbol*)> &multiply_by_c1) {
    TransitionMap transitions2;
    std::map<State, int> topStateIsLeftOrRight, childStateIsLeftOrRight; // 0b10: original tree, 0b01: copied tree, 0b11: both trees
    std::map<State, State> topStateMap, childStateMap;
    // If a state has only one tree, then its id does not change. In this case, it is not present in this map.
    // If a state has two trees, then it presents in this map and its value is the id in the copied tree.

    // Convert from TransitionMap to InternalTransitionMap.
    InternalTransitionMap internalTransitions(qubitNum + 1); // only contains qubits from t to the bottom
    TransitionMap leafTransitions;
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
    for (int q = t; q <= qubitNum; q++) {
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
            for (const auto &kv : childStateIsLeftOrRight) {
                if (kv.second == 0b11) {
                    childStateMap[kv.first] = stateNum;
                    stateNum++;
                }
            }
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
            for (const auto &kv : childStateIsLeftOrRight) {
                if (kv.second == 0b11) {
                    childStateMap[kv.first] = stateNum;
                    stateNum++;
                }
            }
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
        topStateMap = childStateMap;
        childStateMap.clear();
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
    if (gateLog) std::cout << "X" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Y(int t) {
    #ifdef TO_QASM
        system(("echo 'y qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    X(t); gateCount--;
    diagonal_gate(t, std::bind(&Symbol::degree90cw, std::placeholders::_1), std::bind(&Symbol::omega_multiplication, std::placeholders::_1, 2));
    // remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    total_gate_time += duration;
    if (gateLog) std::cout << "Y" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Z(int t, bool opt) {
    #ifdef TO_QASM
        system(("echo 'z qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    diagonal_gate(t, [](Symbol*) {}, std::bind(&Symbol::negate, std::placeholders::_1));
    if (opt) {
        // remove_useless();
        reduce();
    }
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    total_gate_time += duration;
    if (gateLog) std::cout << "Z" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

#define L(s1, s2) (stateNum + (s1) * stateNum + (s2))
#define R(s1, s2) (stateNum + stateNum * stateNum + (s1) * stateNum + (s2))
template <typename Symbol>
void AUTOQ::Automata<Symbol>::General_Single_Qubit_Gate(int t, const std::function<Symbol(const Symbol&, const Symbol&)> &u1u2, const std::function<Symbol(const Symbol&, const Symbol&)> &u3u4) {
    AUTOQ::Automata<Symbol> result;
    result.name = name;
    result.qubitNum = qubitNum;
    result.isTopdownDeterministic = isTopdownDeterministic; // IMPORTANT: Avoid missing copying new fields afterwards.
    result.finalStates = finalStates;

    bool overflow = (stateNum > (std::numeric_limits<State>::max()-stateNum) / stateNum / 2); // want: 2 * stateNum^2 + stateNum <= max
    if (overflow)
        throw std::overflow_error("[ERROR] The number of states after multiplication is too large.");
    // s < stateNum -> s
    // (s1, s2, L) -> stateNum + s1 * stateNum + s2
    // (s1, s2, R) -> stateNum + stateNum^2 + s1 * stateNum + s2 -> max == 2 * stateNum^2 + stateNum

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
    std::map<State, std::map<Tag, std::vector<std::pair<Symbol, StateVector>>>> qcfi;
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
                    if (possible_previous_level_states[L(top1, top2)]) {
                        auto &ref = qcfi[L(top1, top2)][color_intersection];
                        for (const auto &in1 : out_ins1.second) {
                            for (const auto &in2 : out_ins2.second) {
                                ref.push_back({it->first.symbol(), {L(in1.at(0), in2.at(0)), L(in1.at(1), in2.at(1))}});
                            }
                        }
                    }
                    if (possible_previous_level_states[R(top1, top2)]) {
                        auto &ref = qcfi[R(top1, top2)][color_intersection];
                        for (const auto &in1 : out_ins1.second) {
                            for (const auto &in2 : out_ins2.second) {
                                ref.push_back({it->first.symbol(), {R(in1.at(0), in2.at(0)), R(in1.at(1), in2.at(1))}});
                            }
                        }
                    }
                }
            }
        }
        if (std::next(it, 1) == transitions.end() || std::next(it, 1)->first.is_leaf() || qubit != std::next(it, 1)->first.symbol().qubit()) { // this layer is finished!
            for (const auto &q_ : qcfi) {
                for (const auto &c_ : q_.second) {
                    for (const auto &f_i : c_.second) {
                        result.transitions[{f_i.first, c_.first}][q_.first].insert(f_i.second);
                        for (const auto &s : f_i.second)
                            possible_next_level_states[s] = true;
                    }
                }
            }
            qcfi = std::map<State, std::map<Tag, std::vector<std::pair<Symbol, StateVector>>>>();
        }
    }

    head = it;
    possible_previous_level_states = possible_next_level_states;
    qcfi = std::map<State, std::map<Tag, std::vector<std::pair<Symbol, StateVector>>>>(); // may be redundant due to LINE 270
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
                    if (possible_previous_level_states[L(top1, top2)]) {
                        qcfi[L(top1, top2)][color_intersection].push_back({u1u2(it->first.symbol(), it2->first.symbol()), {}});
                    }
                    if (possible_previous_level_states[R(top1, top2)]) {
                        qcfi[R(top1, top2)][color_intersection].push_back({u3u4(it->first.symbol(), it2->first.symbol()), {}});
                    }
                }
            }
        }
    }
    for (const auto &q_ : qcfi) {
        for (const auto &c_ : q_.second) {
            for (const auto &f_i : c_.second) {
                result.transitions[{f_i.first, c_.first}][q_.first].insert(f_i.second);
            }
        }
    }
    result.stateNum = 2 * stateNum * stateNum + stateNum;
    result.state_renumbering();
    result.reduce();
    *this = result;
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
    total_gate_time += duration;
    if (gateLog) std::cout << "H" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::S(int t) {
    #ifdef TO_QASM
        system(("echo 's qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    diagonal_gate(t, [](Symbol*) {}, std::bind(&Symbol::omega_multiplication, std::placeholders::_1, 2));
    // remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    total_gate_time += duration;
    if (gateLog) std::cout << "S" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::T(int t) {
    #ifdef TO_QASM
        system(("echo 't qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    diagonal_gate(t, [](Symbol*) {}, std::bind(&Symbol::omega_multiplication, std::placeholders::_1, 1));
    // remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    total_gate_time += duration;
    if (gateLog) std::cout << "T" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
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
    total_gate_time += duration;
    if (gateLog) std::cout << "Rx" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
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
    total_gate_time += duration;
    if (gateLog) std::cout << "Ry" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
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
    diagonal_gate(t, std::bind(&Symbol::counterclockwise, std::placeholders::_1, -theta / 2), std::bind(&Symbol::counterclockwise, std::placeholders::_1, theta / 2));
    // remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    total_gate_time += duration;
    if (gateLog) std::cout << "Rz" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

// IMPORTANT: Leave the space of size stateNum + aut2.stateNum for the original two automata!
// #define construct_product_state_id(a, b, i) \
//     State i = stateNum + aut2.stateNum + a * aut2.stateNum + b;
// template <typename Symbol>
// void AUTOQ::Automata<Symbol>::General_Controlled_Gate(int c, const AUTOQ::Automata<Symbol> &aut2) {
//     AUTOQ::Automata<Symbol> result;
//     result.name = name;
//     result.qubitNum = qubitNum;
//     result.isTopdownDeterministic = isTopdownDeterministic; // IMPORTANT: Avoid missing copying new fields afterwards.

//     // std::map<std::pair<State, State>, State> stateOldToNew; // used only if overflow := true;
//     bool overflow = (stateNum > std::numeric_limits<State>::max() / aut2.stateNum);
//     if (!overflow)
//         result.finalStates.reserve(finalStates.size() * aut2.finalStates.size()); // TODO: Can we set the initial capacity?
//     else
//         throw std::overflow_error("[ERROR] The number of states after multiplication is too large.");

//     // We assume here transitions are ordered by symbols.
//     // x_i are placed in the beginning, and leaves are placed in the end.
//     // This traversal method is due to efficiency.
//     std::vector<bool> possible_previous_level_states(stateNum + aut2.stateNum + stateNum * aut2.stateNum);
//     std::vector<bool> possible_next_level_states(stateNum + aut2.stateNum + stateNum * aut2.stateNum);
//     for (const auto &fs1 : finalStates) {
//         for (const auto &fs2 : aut2.finalStates) {
//             construct_product_state_id(fs1, fs2, s);
//             possible_previous_level_states[s] = true;
//         }
//     }
//     auto it = transitions.begin(); // global pointer
//     auto head = aut2.transitions.begin();
//     auto tail = head; // just borrow its type to declare the variable
//     std::map<Symbol, std::map<State, std::map<Tag, std::vector<StateVector>>>> fqci;
//     for (; it != transitions.end(); it++) { // iterate over all internal transitions of symbol < c
//         if (it->first.is_leaf()) break; // assert internal transition
//         if (it->first.symbol().qubit() >= c) {
//             head = tail; // for future use
//             break;
//         }
//         if (it->first.symbol().qubit() != head->first.symbol().qubit()) { // change layer
//             head = tail;
//             possible_previous_level_states = possible_next_level_states;
//         }
//         for (auto it2 = head; it2 != aut2.transitions.end(); it2++) {
//             if (it2->first.is_leaf()) break; // another internal transition
//             if (it2->first.symbol().qubit() != it->first.symbol().qubit()) {
//                 tail = it2;
//                 break; // ensure that the two symbols have the same qubit.
//             }
//             assert(it->first.symbol() == it2->first.symbol());
//             for (const auto &in_out1 : it->second) {
//                 assert(in_out1.first.size() == 2);
//                 for (const auto &in_out2 : it2->second) {
//                     assert(in_out2.first.size() == 2);
//                     for (const auto &top1 : in_out1.second) {
//                         for (const auto &top2 : in_out2.second) {
//                             construct_product_state_id(top1, top2, T);
//                             if (possible_previous_level_states[T]) {
//                                 construct_product_state_id(in_out1.first.at(0), in_out2.first.at(0), L);
//                                 construct_product_state_id(in_out1.first.at(1), in_out2.first.at(1), R);
//                                 fqci[it->first.symbol()][T][it->first.tag() & it2->first.tag()].push_back({L, R});
//                             }
//                         }
//                     }
//                 }
//             }
//         }
//         if (std::next(it, 1) == transitions.end() || std::next(it, 1)->first.is_leaf() || it->first.symbol().qubit() != std::next(it, 1)->first.symbol().qubit()) { // this layer is finished!
//             std::map<Symbol, std::map<State, std::vector<Tag>>> delete_colors;
//             for (const auto &f_ : fqci) {
//                 for (const auto &q_ : f_.second) {
//                     for (auto q_ptr = q_.second.rbegin(); q_ptr != q_.second.rend(); ++q_ptr) {
//                         if (q_ptr->second.size() >= 2) {
//                             delete_colors[f_.first][q_.first].push_back(q_ptr->first);
//                         }
//                         else {
//                             for (auto q_ptr2 = q_.second.begin(); q_ptr2 != q_.second.end(); ++q_ptr2) {
//                                 if (q_ptr2->first >= q_ptr->first) break;
//                                 if ((q_ptr->first & q_ptr2->first) == q_ptr->first) {
//                                     delete_colors[f_.first][q_.first].push_back(q_ptr->first);
//                                     break;
//                                 }
//                             }
//                         }
//                     }
//                 }
//             }
//             for (const auto &f_ : fqci) {
//                 for (const auto &q_ : f_.second) {
//                     for (const auto &c_ : q_.second) {
//                         auto &dcfq = delete_colors[f_.first][q_.first];
//                         if (std::find(dcfq.begin(), dcfq.end(), c_.first) != dcfq.end()) continue;
//                         for (const auto &in : c_.second) {
//                             if (it->first.symbol().qubit() == 1) // remember to add final states
//                                 result.finalStates.push_back(q_.first);
//                             result.transitions[{f_.first, c_.first}][in].insert(q_.first);
//                             for (const auto &s : in)
//                                 possible_next_level_states[s] = true;
//                         }
//                     }
//                 }
//             }
//             fqci = std::map<Symbol, std::map<State, std::map<Tag, std::vector<StateVector>>>>();
//         }
//     }

//     possible_previous_level_states = possible_next_level_states;
//     for (; it != transitions.end(); it++) { // iterate over all internal transitions of symbol == c
//         if (it->first.is_leaf()) break; // assert internal transition
//         if (it->first.symbol().qubit() > c) break;
//         auto it2 = head;
//         for (; it2 != aut2.transitions.end(); it2++) {
//             if (it2->first.is_leaf()) break; // another internal transition
//             if (it2->first.symbol().qubit() != it->first.symbol().qubit()) break; // ensure that the two symbols have the same qubit.
//             assert(it->first.symbol() == it2->first.symbol());
//             for (const auto &in_out1 : it->second) {
//                 assert(in_out1.first.size() == 2);
//                 for (const auto &in_out2 : it2->second) {
//                     assert(in_out2.first.size() == 2);
//                     for (const auto &top1 : in_out1.second) {
//                         for (const auto &top2 : in_out2.second) {
//                             construct_product_state_id(top1, top2, T);
//                             if (possible_previous_level_states[T])
//                                 fqci[it->first.symbol()][T][it->first.tag() & it2->first.tag()].push_back({in_out1.first.at(0), stateNum + in_out2.first.at(1)});
//                                 // IMPORTANT: Aut2's state ids must be added by aut1's state number to become the global state ids.
//                         }
//                     }
//                 }
//             }
//         }
//         tail = it2; // for future use
//     }
//     std::map<Symbol, std::map<State, std::vector<Tag>>> delete_colors;
//     for (const auto &f_ : fqci) {
//         for (const auto &q_ : f_.second) {
//             for (auto q_ptr = q_.second.rbegin(); q_ptr != q_.second.rend(); ++q_ptr) {
//                 if (q_ptr->second.size() >= 2) {
//                     delete_colors[f_.first][q_.first].push_back(q_ptr->first);
//                 }
//                 else {
//                     for (auto q_ptr2 = q_.second.begin(); q_ptr2 != q_.second.end(); ++q_ptr2) {
//                         if (q_ptr2->first >= q_ptr->first) break;
//                         if ((q_ptr->first & q_ptr2->first) == q_ptr->first) {
//                             delete_colors[f_.first][q_.first].push_back(q_ptr->first);
//                             break;
//                         }
//                     }
//                 }
//             }
//         }
//     }
//     for (const auto &f_ : fqci) {
//         for (const auto &q_ : f_.second) {
//             for (const auto &c_ : q_.second) {
//                 auto &dcfq = delete_colors[f_.first][q_.first];
//                 if (std::find(dcfq.begin(), dcfq.end(), c_.first) != dcfq.end()) continue;
//                 for (const auto &in : c_.second) {
//                     if (c == 1) result.finalStates.push_back(q_.first);  // remember to add final states
//                     result.transitions[{f_.first, c_.first}][in].insert(q_.first);
//                     for (const auto &s : in)
//                         possible_next_level_states[s] = true;
//                 }
//             }
//         }
//     }
//     fqci = std::map<Symbol, std::map<State, std::map<Tag, std::vector<StateVector>>>>();

//     auto it2 = tail; // global pointer now
//     possible_previous_level_states = possible_next_level_states;
//     for (; it != transitions.end(); it++) { // iterate over all internal transitions of symbol > c
//         if (it->first.is_leaf()) break; // assert internal transition
//         assert(it->first.symbol().qubit() > c);
//         for (const auto &in_outs : it->second) {
//             assert(in_outs.first.size() == 2);
//             for (const auto &top : in_outs.second) {
//                 if (possible_previous_level_states[top])
//                     fqci[it->first.symbol()][top][it->first.tag()].push_back(in_outs.first);
//             }
//         }

//         if (std::next(it, 1) == transitions.end() || std::next(it, 1)->first.is_leaf() || it->first.symbol().qubit() != std::next(it, 1)->first.symbol().qubit()) { // this layer is finished!
//             for (; it2 != aut2.transitions.end(); it2++) {
//                 if (it2->first.is_leaf()) break; // another internal transition
//                 if (it2->first.symbol().qubit() != it->first.symbol().qubit()) break; // ensure that the two symbols have the same qubit.
//                 assert(it->first.symbol() == it2->first.symbol());
//                 for (const auto &in_outs : it2->second) {
//                     assert(in_outs.first.size() == 2);
//                     for (const auto &top : in_outs.second) {
//                         if (possible_previous_level_states[top+stateNum]) // IMPORTANT: Aut2's state ids must be added by aut1's state number to become the global state ids.
//                             fqci[it2->first.symbol()][top+stateNum][it2->first.tag()].push_back({in_outs.first.at(0)+stateNum, in_outs.first.at(1)+stateNum});
//                     }
//                 }
//             }

//             std::map<Symbol, std::map<State, std::vector<Tag>>> delete_colors;
//             for (const auto &f_ : fqci) {
//                 for (const auto &q_ : f_.second) {
//                     for (auto q_ptr = q_.second.rbegin(); q_ptr != q_.second.rend(); ++q_ptr) {
//                         if (q_ptr->second.size() >= 2) {
//                             delete_colors[f_.first][q_.first].push_back(q_ptr->first);
//                         }
//                         else {
//                             for (auto q_ptr2 = q_.second.begin(); q_ptr2 != q_.second.end(); ++q_ptr2) {
//                                 if (q_ptr2->first >= q_ptr->first) break;
//                                 if ((q_ptr->first & q_ptr2->first) == q_ptr->first) {
//                                     delete_colors[f_.first][q_.first].push_back(q_ptr->first);
//                                     break;
//                                 }
//                             }
//                         }
//                     }
//                 }
//             }
//             for (const auto &f_ : fqci) {
//                 for (const auto &q_ : f_.second) {
//                     for (const auto &c_ : q_.second) {
//                         auto &dcfq = delete_colors[f_.first][q_.first];
//                         if (std::find(dcfq.begin(), dcfq.end(), c_.first) != dcfq.end()) continue;
//                         for (const auto &in : c_.second) {
//                             result.transitions[{f_.first, c_.first}][in].insert(q_.first);
//                             for (const auto &s : in)
//                                 possible_next_level_states[s] = true;
//                         }
//                     }
//                 }
//             }
//             fqci = std::map<Symbol, std::map<State, std::map<Tag, std::vector<StateVector>>>>();
//             possible_previous_level_states = possible_next_level_states;
//         }
//     }
//     possible_previous_level_states = possible_next_level_states;
//     for (; it != transitions.end(); it++) { // iterate over all leaf transitions of aut1
//         for (const auto &in_outs : it->second) {
//             assert(in_outs.first.size() == 0);
//             for (const auto &top : in_outs.second) {
//                 if (possible_previous_level_states[top])
//                     fqci[it->first.symbol()][top][it->first.tag()].push_back({});
//             }
//         }
//     }
//     for (; it2 != aut2.transitions.end(); it2++) { // iterate over all leaf transitions of aut2
//         for (const auto &in_outs : it2->second) {
//             assert(in_outs.first.size() == 0);
//             for (const auto &top : in_outs.second) {
//                 if (possible_previous_level_states[top+stateNum]) // IMPORTANT: Aut2's state ids must be added by aut1's state number to become the global state ids.
//                     fqci[it2->first.symbol()][top+stateNum][it2->first.tag()].push_back({});
//             }
//         }
//     }
//     delete_colors.clear();
//     for (const auto &f_ : fqci) {
//         for (const auto &q_ : f_.second) {
//             for (auto q_ptr = q_.second.rbegin(); q_ptr != q_.second.rend(); ++q_ptr) {
//                 if (q_ptr->second.size() >= 2) {
//                     delete_colors[f_.first][q_.first].push_back(q_ptr->first);
//                 }
//                 else {
//                     for (auto q_ptr2 = q_.second.begin(); q_ptr2 != q_.second.end(); ++q_ptr2) {
//                         if (q_ptr2->first >= q_ptr->first) break;
//                         if ((q_ptr->first & q_ptr2->first) == q_ptr->first) {
//                             delete_colors[f_.first][q_.first].push_back(q_ptr->first);
//                             break;
//                         }
//                     }
//                 }
//             }
//         }
//     }
//     for (const auto &f_ : fqci) {
//         for (const auto &q_ : f_.second) {
//             for (const auto &c_ : q_.second) {
//                 auto &dcfq = delete_colors[f_.first][q_.first];
//                 if (std::find(dcfq.begin(), dcfq.end(), c_.first) != dcfq.end()) continue;
//                 for (const auto &in : c_.second) {
//                     result.transitions[{f_.first, c_.first}][in].insert(q_.first);
//                     for (const auto &s : in)
//                         possible_next_level_states[s] = true;
//                 }
//             }
//         }
//     }
//     result.stateNum = stateNum + aut2.stateNum + stateNum * aut2.stateNum;
//     result.state_renumbering();
//     result.reduce();
//     *this = result;
// }

template <typename Symbol>
void AUTOQ::Automata<Symbol>::CX(int c, int t, bool opt) {
    #ifdef TO_QASM
        system(("echo 'cx qubits[" + std::to_string(c-1) + "], qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    assert(c != t);
    if (c > t) {
        H(c); gateCount--;
        H(t); gateCount--;
        CX(t, c); gateCount--;
        H(c); gateCount--;
        H(t); gateCount--;
    } else {
        TransitionMap transitions2;
        std::map<State, int> topStateIsLeftOrRight, childStateIsLeftOrRight; // 0b10: original tree, 0b01: copied tree, 0b11: both trees
        std::map<State, State> topStateMap, childStateMap;
        // If a state has only one tree, then its id does not change. In this case, it is not present in this map.
        // If a state has two trees, then it presents in this map and its value is the id in the copied tree.

        // Convert from TransitionMap to InternalTransitionMap.
        InternalTransitionMap internalTransitions(qubitNum + 1); // only contains qubits from c to the bottom
        TransitionMap leafTransitions;
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
                for (const auto &kv : childStateIsLeftOrRight) {
                    if (kv.second == 0b11) {
                        childStateMap[kv.first] = stateNum;
                        stateNum++;
                    }
                }
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
                for (const auto &kv : childStateIsLeftOrRight) {
                    if (kv.second == 0b11) {
                        childStateMap[kv.first] = stateNum;
                        stateNum++;
                    }
                }
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
            topStateMap = childStateMap;
            childStateMap.clear();
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
        if (opt) {
            // remove_useless();
            reduce();
        }
        auto duration = std::chrono::steady_clock::now() - start;
        total_gate_time += duration;
    }
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "CX" << c << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

#define queryTopID2(oldID, newID) \
    State newID;    \
    {   \
        auto it = topStateMap2.find(oldID);    \
        if (it == topStateMap2.end()) {   \
            it = topStateMap.find(oldID);  \
            if (it == topStateMap.end()) {    \
                newID = oldID;    \
            } else { \
                newID = it->second; \
            }   \
        } else {   \
            newID = it->second; \
        }   \
    }
#define queryChildID2(oldID, newID) \
    State newID;    \
    {   \
        auto it = childStateMap2.find(oldID);    \
        if (it == childStateMap2.end()) {   \
            it = childStateMap.find(oldID);  \
            if (it == childStateMap.end()) {    \
                newID = oldID;    \
            } else { \
                newID = it->second; \
            }   \
        } else {   \
            newID = it->second; \
        }   \
    }
template <typename Symbol>
void AUTOQ::Automata<Symbol>::CZ(int c, int t) {
    #ifdef TO_QASM
        system(("echo 'cz qubits[" + std::to_string(c-1) + "], qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    assert(c != t);
    if (c > t) std::swap(c, t);
    auto start = std::chrono::steady_clock::now();
    TransitionMap transitions2;
    std::map<State, int> topStateIsLeftOrRight, childStateIsLeftOrRight; // 0b10: original tree, 0b01: copied tree, 0b11: both trees
    std::map<State, State> topStateMap, childStateMap;
    std::map<State, int> topStateIsLeftOrRight2, childStateIsLeftOrRight2; // 0b10: original tree, 0b01: copied tree, 0b11: both trees
    std::map<State, State> topStateMap2, childStateMap2;
    // If a state has only one tree, then its id does not change. In this case, it is not present in this map.
    // If a state has two trees, then it presents in this map and its value is the id in the copied tree.

    // Convert from TransitionMap to InternalTransitionMap.
    InternalTransitionMap internalTransitions(qubitNum + 1); // only contains qubits from c to the bottom
    TransitionMap leafTransitions;
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
            for (const auto &kv : childStateIsLeftOrRight) {
                if (kv.second == 0b11) {
                    childStateMap[kv.first] = stateNum;
                    stateNum++;
                }
            }
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
            for (const auto &kv : childStateIsLeftOrRight) {
                if (kv.second == 0b11) {
                    childStateMap[kv.first] = stateNum;
                    stateNum++;
                }
            }
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
            for (const auto &kv : childStateIsLeftOrRight) {
                if (kv.second == 0b11) {
                    childStateMap[kv.first] = stateNum;
                    stateNum++;
                }
            }
            for (const auto &kv : childStateIsLeftOrRight2) {
                if (kv.second == 0b11) {
                    childStateMap2[kv.first] = stateNum;
                    stateNum++;
                }
            }
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
            for (const auto &kv : childStateIsLeftOrRight) {
                if (kv.second == 0b11) {
                    childStateMap[kv.first] = stateNum;
                    stateNum++;
                }
            }
            for (const auto &kv : childStateIsLeftOrRight2) {
                if (kv.second == 0b11) {
                    childStateMap2[kv.first] = stateNum;
                    stateNum++;
                }
            }
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
        topStateMap = childStateMap;
        childStateMap.clear();
        topStateIsLeftOrRight2 = childStateIsLeftOrRight2;
        childStateIsLeftOrRight2.clear();
        topStateMap2 = childStateMap2;
        childStateMap2.clear();
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
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    total_gate_time += duration;
    if (gateLog) std::cout << "CZ" << c << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
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
        auto start = std::chrono::steady_clock::now();
        TransitionMap transitions2;
        std::map<State, int> topStateIsLeftOrRight, childStateIsLeftOrRight; // 0b10: original tree, 0b01: copied tree, 0b11: both trees
        std::map<State, State> topStateMap, childStateMap;
        std::map<State, int> topStateIsLeftOrRight2, childStateIsLeftOrRight2; // 0b10: original tree, 0b01: copied tree, 0b11: both trees
        std::map<State, State> topStateMap2, childStateMap2;
        // If a state has only one tree, then its id does not change. In this case, it is not present in this map.
        // If a state has two trees, then it presents in this map and its value is the id in the copied tree.

        // Convert from TransitionMap to InternalTransitionMap.
        InternalTransitionMap internalTransitions(qubitNum + 1); // only contains qubits from c to the bottom
        TransitionMap leafTransitions;
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
                for (const auto &kv : childStateIsLeftOrRight) {
                    if (kv.second == 0b11) {
                        childStateMap[kv.first] = stateNum;
                        stateNum++;
                    }
                }
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
                for (const auto &kv : childStateIsLeftOrRight) {
                    if (kv.second == 0b11) {
                        childStateMap[kv.first] = stateNum;
                        stateNum++;
                    }
                }
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
                for (const auto &kv : childStateIsLeftOrRight) {
                    if (kv.second == 0b11) {
                        childStateMap[kv.first] = stateNum;
                        stateNum++;
                    }
                }
                for (const auto &kv : childStateIsLeftOrRight2) {
                    if (kv.second == 0b11) {
                        childStateMap2[kv.first] = stateNum;
                        stateNum++;
                    }
                }
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
                for (const auto &kv : childStateIsLeftOrRight) {
                    if (kv.second == 0b11) {
                        childStateMap[kv.first] = stateNum;
                        stateNum++;
                    }
                }
                for (const auto &kv : childStateIsLeftOrRight2) {
                    if (kv.second == 0b11) {
                        childStateMap2[kv.first] = stateNum;
                        stateNum++;
                    }
                }
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
            topStateMap = childStateMap;
            childStateMap.clear();
            topStateIsLeftOrRight2 = childStateIsLeftOrRight2;
            childStateIsLeftOrRight2.clear();
            topStateMap2 = childStateMap2;
            childStateMap2.clear();
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
        reduce();
        auto duration = std::chrono::steady_clock::now() - start;
        total_gate_time += duration;
    } else if (t < c) { // t < c < c2
        H(c2); gateCount--;
        H(t); gateCount--;
        CCX(t, c, c2); gateCount--;
        H(c2); gateCount--;
        H(t); gateCount--;
    } else { // c < t < c2
        H(c2); gateCount--;
        H(t); gateCount--;
        CCX(c, t, c2); gateCount--;
        H(c2); gateCount--;
        H(t); gateCount--;
    }
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "CCX" << c << "," << c2 << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Tdg(int t) {
    // #ifdef TO_QASM
    //     system(("echo 'tdg qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
    //     return;
    // #endif
    auto start = std::chrono::steady_clock::now();
    diagonal_gate(t, [](Symbol*) {}, std::bind(&Symbol::degree45cw, std::placeholders::_1));
    // remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    total_gate_time += duration;
    if (gateLog) std::cout << "Tdg" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Sdg(int t) {
    // #ifdef TO_QASM
    //     system(("echo 'sdg qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
    //     return;
    // #endif
    auto start = std::chrono::steady_clock::now();
    diagonal_gate(t, [](Symbol*) {}, std::bind(&Symbol::degree90cw, std::placeholders::_1));
    // remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    total_gate_time += duration;
    if (gateLog) std::cout << "Sdg" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::swap(int t1, int t2) {
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
    if (gateLog) std::cout << "swap" << t1 << "," << t2 << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

// void AUTOQ::Automata<Symbol>::Fredkin(int c, int t, int t2) {
//     auto start = std::chrono::steady_clock::now();
//     assert(c != t && t != t2 && t2 != c);
//     this->semi_determinize();
//     auto aut1 = *this;
//     aut1.branch_restriction(c, false);
//     auto aut2 = *this;
//     aut2.branch_restriction(c, true);
//     auto aut3 = aut2;
//     auto aut4 = aut2;
//     auto aut5 = aut2;
//     aut2.branch_restriction(t, true);
//     aut2.branch_restriction(t2, true);
//     aut3.branch_restriction(t, false);
//     aut3.branch_restriction(t2, false);
//     aut4.value_restriction(t, false);
//     aut4.value_restriction(t2, true);
//     aut4.branch_restriction(t2, false);
//     aut4.branch_restriction(t, true);
//     aut5.value_restriction(t, true);
//     aut5.value_restriction(t2, false);
//     aut5.branch_restriction(t2, true);
//     aut5.branch_restriction(t, false);
//     *this = aut1 + aut2 + aut3 + aut4 + aut5;
//     this->semi_undeterminize();
//     gateCount++;
//     auto duration = std::chrono::steady_clock::now() - start;
//     if (gateLog) std::cout << "Fredkin" << c << "," << t << "," << t2 << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
// }

template <typename Symbol>
void AUTOQ::Automata<Symbol>::randG(int G, int A, int B, int C) {
    int g, a, b, c;
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