#include <autoq/aut_description.hh>
#include <functional>

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

template <typename Symbol>
void AUTOQ::Automata<Symbol>::X(int k) {
    #ifdef TO_QASM
        system(("echo 'x qubits[" + std::to_string(k-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    auto transitions_copy = transitions;
    for (const auto &t : transitions_copy) {
        const auto &symbol_tag = t.first;
        if (symbol_tag.is_internal() && symbol_tag.symbol().qubit() == k) {
            transitions.erase(symbol_tag);
            for (const auto &in_out : t.second) {
                assert(in_out.first.size() == 2);
                transitions[symbol_tag][{in_out.first[1], in_out.first[0]}] = in_out.second;
            }
        }
    }
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "X" << k << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Y(int k) {
    #ifdef TO_QASM
        system(("echo 'y qubits[" + std::to_string(k-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    TransitionMap transitions_copy = transitions;
    for (const auto &t : transitions_copy) {
        SymbolTag symbol_tag = t.first;
        if (symbol_tag.is_leaf())
            symbol_tag.symbol().negate();
        if (!(symbol_tag.is_internal() && symbol_tag.symbol().qubit() <= k)) {
            for (const auto &in_out : t.second) {
                StateVector in;
                for (const auto &s : in_out.first)
                    in.push_back(s+stateNum);
                for (const auto &s : in_out.second)
                    transitions[symbol_tag][in].insert(s+stateNum);
            }
        }
    }
    for (auto &tr : transitions) {
        if (tr.first.is_leaf() || (tr.first.is_internal() && tr.first.symbol().qubit() > k)) break;
        if (tr.first.is_internal() && tr.first.symbol().qubit() == k) {
            auto in_outs = tr.second;
            for (const auto &in_out : in_outs) {
                assert(in_out.first.size() == 2);
                if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
                    tr.second[{in_out.first[1]+stateNum, in_out.first[0]}] = in_out.second;
                    tr.second.erase(in_out.first);
                }
            }
        }
    }
    stateNum *= 2;
    omega_multiplication(2);
    remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "Y" << k << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Z(int t) {
    #ifdef TO_QASM
        system(("echo 'z qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    TransitionMap transitions_copy = transitions;
    for (const auto &tr : transitions_copy) {
        SymbolTag symbol_tag = tr.first;
        if (symbol_tag.is_leaf())
            symbol_tag.symbol().negate();
        if (!(symbol_tag.is_internal() && symbol_tag.symbol().qubit() <= t)) {
            for (const auto &in_out : tr.second) {
                StateVector in;
                for (const auto &s : in_out.first)
                    in.push_back(s+stateNum);
                for (const auto &s : in_out.second)
                    transitions[symbol_tag][in].insert(s+stateNum);
            }
        }
    } 
    for (auto &tr : transitions) {
        if (tr.first.is_leaf() || (tr.first.is_internal() && tr.first.symbol().qubit() > t)) break;
        if (tr.first.is_internal() && tr.first.symbol().qubit() == t) {
            auto in_outs = tr.second;
            for (const auto &in_out : in_outs) {
                assert(in_out.first.size() == 2);
                if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
                    tr.second[{in_out.first[0], in_out.first[1]+stateNum}] = in_out.second;
                    tr.second.erase(in_out.first);
                }
            }
        }
    }
    stateNum *= 2;
    remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "Z" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::General_Single_Qubit_Gate(int t, std::function<Symbol(const Symbol&, const Symbol&)> L, std::function<Symbol(const Symbol&, const Symbol&)> R) {
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

    std::vector<bool> possible_next_level_states(2 * stateNum * stateNum + stateNum);
    assert(it->first.symbol().qubit() == t); // iterate over all internal transitions of symbol == t
    for (; it != transitions.end(); it++) { 
        if (it->first.is_leaf() || it->first.symbol().qubit() > t) break;
        for (const auto &in_outs : it->second) {
            assert(in_outs.first.size() == 2);
            result.transitions[it->first][{stateNum + in_outs.first.at(0)*stateNum + in_outs.first.at(1),
                       stateNum + stateNum*stateNum + in_outs.first.at(0)*stateNum + in_outs.first.at(1)}]
                = in_outs.second;
            possible_next_level_states[stateNum + in_outs.first.at(0)*stateNum + in_outs.first.at(1)] = true;
            possible_next_level_states[stateNum + stateNum*stateNum + in_outs.first.at(0)*stateNum + in_outs.first.at(1)] = true;
        }
    }

    auto head = it;
    std::map<Symbol, std::map<State, std::map<Tag, std::vector<StateVector>>>> fqci;
    std::vector<bool> possible_previous_level_states = possible_next_level_states;
    for (; it != transitions.end(); it++) { // iterate over all internal transitions of symbol > t
        if (it->first.is_leaf()) break; // assert internal transition
        assert(it->first.symbol().qubit() > t);
        if (it->first.symbol().qubit() != head->first.symbol().qubit()) { // change layer
            head = it;
            possible_previous_level_states = possible_next_level_states;
        }
        for (auto it2=head; it2 != transitions.end(); it2++) {
            if (it2->first.is_leaf()) break; // another internal transition
            if (it2->first.symbol().qubit() != it->first.symbol().qubit()) break; // ensure that the two symbols have the same qubit.
            assert(it->first.symbol() == it2->first.symbol());
            for (const auto &in_out1 : it->second) {
                assert(in_out1.first.size() == 2);
                for (const auto &in_out2 : it2->second) {
                    assert(in_out2.first.size() == 2);
                    for (const auto &top1 : in_out1.second) {
                        for (const auto &top2 : in_out2.second) {
                            // nt is short for the new transition
                            // std::cout << AUTOQ::Util::Convert::ToString(in_out1.first) << "A\n";
                            // std::cout << AUTOQ::Util::Convert::ToString(in_out2.first) << "B\n";
                            // std::cout << "(" << stateNum + in_out1.first.at(0)*stateNum + in_out2.first.at(0) << ")("
                            //                  << stateNum + in_out1.first.at(1)*stateNum + in_out2.first.at(1) << ")("
                            //                  << top1 << ")(" << top2 << ")(" << stateNum + top1*stateNum + top2 << ")\n";
                            // auto &nt = result.transitions[{it->first.symbol(), it->first.tag() | it2->first.tag()}];
                            if (possible_previous_level_states[stateNum + top1*stateNum + top2]) {
                                fqci[it->first.symbol()][stateNum + top1*stateNum + top2][it->first.tag() | it2->first.tag()].push_back({stateNum + in_out1.first.at(0)*stateNum + in_out2.first.at(0), stateNum + in_out1.first.at(1)*stateNum + in_out2.first.at(1)});
                                // nt[{stateNum + in_out1.first.at(0)*stateNum + in_out2.first.at(0),
                                //     stateNum + in_out1.first.at(1)*stateNum + in_out2.first.at(1)}]
                                //     .insert(stateNum + top1*stateNum + top2); // (s1, s2, +) -> stateNum + s1 * stateNum + s2
                                // possible_next_level_states[stateNum + in_out1.first.at(0)*stateNum + in_out2.first.at(0)] = true;
                                // possible_next_level_states[stateNum + in_out1.first.at(1)*stateNum + in_out2.first.at(1)] = true;
                            }
                            if (possible_previous_level_states[stateNum + stateNum*stateNum + top1*stateNum + top2]) {
                                fqci[it->first.symbol()][stateNum + stateNum*stateNum + top1*stateNum + top2][it->first.tag() | it2->first.tag()].push_back({stateNum + stateNum*stateNum + in_out1.first.at(0)*stateNum + in_out2.first.at(0), stateNum + stateNum*stateNum + in_out1.first.at(1)*stateNum + in_out2.first.at(1)});
                                // nt[{stateNum + stateNum*stateNum + in_out1.first.at(0)*stateNum + in_out2.first.at(0),
                                //     stateNum + stateNum*stateNum + in_out1.first.at(1)*stateNum + in_out2.first.at(1)}]
                                //     .insert(stateNum + stateNum*stateNum + top1*stateNum + top2); // (s1, s2, -) -> stateNum + stateNum^2 + s1 * stateNum + s2
                                // possible_next_level_states[stateNum + stateNum*stateNum + in_out1.first.at(0)*stateNum + in_out2.first.at(0)] = true;
                                // possible_next_level_states[stateNum + stateNum*stateNum + in_out1.first.at(1)*stateNum + in_out2.first.at(1)] = true;
                            }
                        }
                    }
                }
            }
        }
        if (std::next(it, 1) == transitions.end() || it->first.symbol().qubit() != std::next(it, 1)->first.symbol().qubit()) { // this layer is finished!
            std::map<Symbol, std::map<State, std::vector<Tag>>> delete_colors;
            for (const auto &f_ : fqci) {
                for (const auto &q_ : f_.second) {
                    for (auto q_ptr = q_.second.rbegin(); q_ptr != q_.second.rend(); ++q_ptr) {
                        if (q_ptr->second.size() >= 2) {
                            delete_colors[f_.first][q_.first].push_back(q_ptr->first);
                        }
                        else {
                            for (auto q_ptr2 = q_.second.begin(); q_ptr2 != q_.second.end(); ++q_ptr2) {
                                if (q_ptr2->first >= q_ptr->first) break;
                                if ((q_ptr->first | q_ptr2->first) == q_ptr->first) {
                                    delete_colors[f_.first][q_.first].push_back(q_ptr->first);
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            for (const auto &f_ : fqci) {
                for (const auto &q_ : f_.second) {
                    for (const auto &c_ : q_.second) {
                        auto &dcfq = delete_colors[f_.first][q_.first];
                        if (std::find(dcfq.begin(), dcfq.end(), c_.first) != dcfq.end()) continue;
                        for (const auto &in : c_.second) {
                            result.transitions[{f_.first, c_.first}][in].insert(q_.first);
                            for (const auto &s : in)
                                possible_next_level_states[s] = true;
                        }
                    }
                }
            }

            fqci = std::map<Symbol, std::map<State, std::map<Tag, std::vector<StateVector>>>>();
        }
    }

    head = it;
    possible_previous_level_states = possible_next_level_states;
    fqci = std::map<Symbol, std::map<State, std::map<Tag, std::vector<StateVector>>>>(); // may be redundant due to LINE 278
    for (; it != transitions.end(); it++) { // iterate over all leaf transitions
        assert(it->first.is_leaf()); // assert leaf transition
        for (auto it2=head; it2 != transitions.end(); it2++) {
            assert(it2->first.is_leaf()); // another leaf transition
            for (const auto &in_out1 : it->second) {
                assert(in_out1.first.size() == 0);
                for (const auto &in_out2 : it2->second) {
                    assert(in_out2.first.size() == 0);
                    // std::cout << AUTOQ::Util::Convert::ToString(in_out1.second) << "++\n";
                    for (const auto &top1 : in_out1.second) {
                        // std::cout << AUTOQ::Util::Convert::ToString(in_out2.second) << "==\n";
                        for (const auto &top2 : in_out2.second) {
                            // std::cout << it->first << "A\n";
                            // std::cout << it2->first << "B\n";
                            // std::cout << (it->first.symbol() + it2->first.symbol()).divide_by_the_square_root_of_two() << "C\n";
                            // std::cout << (it->first.symbol() - it2->first.symbol()).divide_by_the_square_root_of_two() << "D\n";
                            // std::cout << "(" << stateNum << ")(" << top1 << ")(" << top2 << ")(" << stateNum + top1*stateNum + top2 << ")(" << stateNum + stateNum*stateNum + top1*stateNum + top2 << ")\n";
                            if (possible_previous_level_states[stateNum + top1*stateNum + top2])
                                fqci[L(it->first.symbol(), it2->first.symbol())][stateNum + top1*stateNum + top2][it->first.tag() | it2->first.tag()].push_back({});
                                // result.transitions[{(it->first.symbol() + it2->first.symbol()).divide_by_the_square_root_of_two(),
                                //                     it->first.tag() | it2->first.tag()}][{}]
                                //     .insert(stateNum + top1*stateNum + top2); // (s1, s2, +) -> stateNum + s1 * stateNum + s2
                            if (possible_previous_level_states[stateNum + stateNum*stateNum + top1*stateNum + top2])
                                fqci[R(it->first.symbol(), it2->first.symbol())][stateNum + stateNum*stateNum + top1*stateNum + top2][it->first.tag() | it2->first.tag()].push_back({});
                                // result.transitions[{(it->first.symbol() - it2->first.symbol()).divide_by_the_square_root_of_two(),
                                //                     it->first.tag() | it2->first.tag()}][{}]
                                //     .insert(stateNum + stateNum*stateNum + top1*stateNum + top2); // (s1, s2, -) -> stateNum + stateNum^2 + s1 * stateNum + s2
                        }
                    }
                }
            }
        }
    }
    std::map<Symbol, std::map<State, std::vector<Tag>>> delete_colors;
    for (const auto &f_ : fqci) {
        for (const auto &q_ : f_.second) {
            for (auto q_ptr = q_.second.rbegin(); q_ptr != q_.second.rend(); ++q_ptr) {
                if (q_ptr->second.size() >= 2) {
                    delete_colors[f_.first][q_.first].push_back(q_ptr->first);
                }
                else {
                    for (auto q_ptr2 = q_.second.begin(); q_ptr2 != q_.second.end(); ++q_ptr2) {
                        if (q_ptr2->first >= q_ptr->first) break;
                        if ((q_ptr->first | q_ptr2->first) == q_ptr->first) {
                            delete_colors[f_.first][q_.first].push_back(q_ptr->first);
                            break;
                        }
                    }
                }
            }
        }
    }
    for (const auto &f_ : fqci) {
        for (const auto &q_ : f_.second) {
            for (const auto &c_ : q_.second) {
                auto &dcfq = delete_colors[f_.first][q_.first];
                if (std::find(dcfq.begin(), dcfq.end(), c_.first) != dcfq.end()) continue;
                for (const auto &in : c_.second) {
                    result.transitions[{f_.first, c_.first}][in].insert(q_.first);
                    // for (const auto &s : in)
                    //     possible_next_level_states[s] = true;
                }
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
    if (gateLog) std::cout << "H" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::S(int t) {
    #ifdef TO_QASM
        system(("echo 's qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    auto aut2 = *this;
    aut2.omega_multiplication(2);
    for (const auto &tr : aut2.transitions) {
        const SymbolTag &symbol_tag = tr.first;
        if (!(symbol_tag.is_internal() && symbol_tag.symbol().qubit() <= t)) {
            auto &ttf = transitions[symbol_tag];
            for (const auto &in_out : tr.second) {
                StateVector in;
                for (const auto &s : in_out.first)
                    in.push_back(s+stateNum);
                for (const auto &s : in_out.second)
                    ttf[in].insert(s+stateNum);
            }
        }
    }
    for (auto &tr : transitions) {
        if (tr.first.is_leaf() || (tr.first.is_internal() && tr.first.symbol().qubit() > t)) break;
        if (tr.first.is_internal() && tr.first.symbol().qubit() == t) {
            auto in_outs = tr.second;
            for (const auto &in_out : in_outs) {
                assert(in_out.first.size() == 2);
                if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
                    tr.second[{in_out.first[0], in_out.first[1]+stateNum}] = in_out.second;
                    tr.second.erase(in_out.first);
                }
            }
        }
    }
    stateNum += aut2.stateNum;
    remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "S" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::T(int t) {
    #ifdef TO_QASM
        system(("echo 't qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    auto aut2 = *this;
    aut2.omega_multiplication();
    for (const auto &tr : aut2.transitions) {
        const SymbolTag &symbol_tag = tr.first;
        if (!(symbol_tag.is_internal() && symbol_tag.symbol().qubit() <= t)) {
            auto &ttf = transitions[symbol_tag];
            for (const auto &in_out : tr.second) {
                StateVector in;
                for (const auto &s : in_out.first)
                    in.push_back(s+stateNum);
                for (const auto &s : in_out.second)
                    ttf[in].insert(s+stateNum);
            }
        }
    }
    for (auto &tr : transitions) {
        if (tr.first.is_leaf() || (tr.first.is_internal() && tr.first.symbol().qubit() > t)) break;
        if (tr.first.is_internal() && tr.first.symbol().qubit() == t) {
            auto in_outs = tr.second;
            for (const auto &in_out : in_outs) {
                assert(in_out.first.size() == 2);
                if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
                    tr.second[{in_out.first[0], in_out.first[1]+stateNum}] = in_out.second;
                    tr.second.erase(in_out.first);
                }
            }
        }
    }
    stateNum += aut2.stateNum;
    remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "T" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Rx(int t) {
    #ifdef TO_QASM
        system(("echo 'rx(pi/2) qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    General_Single_Qubit_Gate(t,
        [](const Symbol &l, Symbol r) -> Symbol { return (l - r.omega_multiplication(2)).divide_by_the_square_root_of_two(); },
        [](Symbol l, const Symbol &r) -> Symbol { return (r - l.omega_multiplication(2)).divide_by_the_square_root_of_two(); });
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
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
    if (gateLog) std::cout << "Ry" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::CNOT(int c, int t, bool opt) {
    #ifdef TO_QASM
        system(("echo 'cx qubits[" + std::to_string(c-1) + "], qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    assert(c != t);
    if (c > t) {
        exit(1);
        // this->semi_determinize();
        // auto aut1 = *this;
        // aut1.branch_restriction(c, false);
        // auto aut2 = *this;
        // aut2.branch_restriction(c, true);
        // auto aut3 = aut2;
        // aut2.value_restriction(t, false);
        // aut2.branch_restriction(t, true);
        // aut3.value_restriction(t, true);
        // aut3.branch_restriction(t, false);
        // *this = aut1 + aut2 + aut3;
        // this->semi_undeterminize();
    } else {
        auto aut2 = *this;
        aut2.X(t); gateCount--; // prevent repeated counting
        for (const auto &tr : aut2.transitions) {
            const SymbolTag &symbol_tag = tr.first;
            if (!(symbol_tag.is_internal() && symbol_tag.symbol().qubit() <= c)) {
                auto &ttf = transitions[symbol_tag];
                for (const auto &in_out : tr.second) {
                    StateVector in;
                    for (const auto &s : in_out.first)
                        in.push_back(s+stateNum);
                    for (const auto &s : in_out.second)
                        ttf[in].insert(s+stateNum);
                }
            }
        }
        for (auto &tr : transitions) {
            if (tr.first.is_leaf() || (tr.first.is_internal() && tr.first.symbol().qubit() > c)) break;
            if (tr.first.is_internal() && tr.first.symbol().qubit() == c) {
                auto in_outs = tr.second;
                for (const auto &in_out : in_outs) {
                    assert(in_out.first.size() == 2);
                    if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
                        tr.second[{in_out.first[0], in_out.first[1]+stateNum}] = in_out.second;
                        tr.second.erase(in_out.first);
                    }
                }
            }
        }
        stateNum += aut2.stateNum;
        if (opt) {
            remove_useless();
            reduce();
        }
    }
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "CNOT" << c << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::CZ(int c, int t) {
    #ifdef TO_QASM
        system(("echo 'cz qubits[" + std::to_string(c-1) + "], qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    assert(c != t);
    if (c > t) std::swap(c, t);
    auto aut2 = *this;
    for (const auto &tr : transitions) {
        SymbolTag symbol_tag = tr.first;
        if (symbol_tag.is_leaf())
            symbol_tag.symbol().negate();
        if (!(symbol_tag.is_internal() && symbol_tag.symbol().qubit() <= t)) {
            for (const auto &in_out : tr.second) {
                StateVector in;
                for (const auto &s : in_out.first)
                    in.push_back(s+stateNum);
                for (const auto &s : in_out.second)
                    aut2.transitions[symbol_tag][in].insert(s+stateNum);
            }
        }
    } 
    for (auto &tr : aut2.transitions) {
        if (tr.first.is_leaf() || (tr.first.is_internal() && tr.first.symbol().qubit() > t)) break;
        if (tr.first.is_internal() && tr.first.symbol().qubit() == t) {
            auto in_outs = tr.second;
            for (const auto &in_out : in_outs) {
                assert(in_out.first.size() == 2);
                if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
                    tr.second[{in_out.first[0], in_out.first[1]+stateNum}] = in_out.second;
                    tr.second.erase(in_out.first);
                }
            }
        }
    }
    for (const auto &tr : aut2.transitions) {
        const SymbolTag &symbol_tag = tr.first;
        if (!(symbol_tag.is_internal() && symbol_tag.symbol().qubit() <= c)) {
            for (const auto &in_out : tr.second) {
                StateVector in;
                for (const auto &s : in_out.first)
                    in.push_back(s+stateNum);
                for (const auto &s : in_out.second)
                    transitions[symbol_tag][in].insert(s+stateNum);
            }
        }
    }   
    for (auto &tr : aut2.transitions) {
        if (tr.first.is_leaf() || (tr.first.is_internal() && tr.first.symbol().qubit() > c)) break;
        if (tr.first.is_internal() && tr.first.symbol().qubit() == c) {
            auto in_outs2 = tr.second;
            for (const auto &in_out : in_outs2) {
                assert(in_out.first.size() == 2);
                if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
                    tr.second[{in_out.first[0], in_out.first[1]+stateNum}] = in_out.second;
                    tr.second.erase(in_out.first);
                }
            }
        }
    }
    stateNum *= 3;
    remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "CZ" << c << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Toffoli(int c, int c2, int t) {
    #ifdef TO_QASM
        system(("echo 'ccx qubits[" + std::to_string(c-1) + "], qubits[" + std::to_string(c2-1) + "], qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    assert(c != c2 && c2 != t && t != c);
    if (c < t && c2 < t) {
        if (c > c2) std::swap(c, c2);
        auto aut2 = *this;
        aut2.CNOT(c2, t, false); gateCount--; // prevent repeated counting
        for (const auto &tr : aut2.transitions) {
            const SymbolTag &symbol_tag = tr.first;
            if (!(symbol_tag.is_internal() && symbol_tag.symbol().qubit() <= c)) {
                auto &ttf = transitions[symbol_tag];
                for (const auto &in_out : tr.second) {
                    StateVector in;
                    for (const auto &s : in_out.first)
                        in.push_back(s+stateNum);
                    for (const auto &s : in_out.second)
                        ttf[in].insert(s+stateNum);
                }
            }
        }
        for (auto &tr : transitions) {
            if (tr.first.is_leaf() || (tr.first.is_internal() && tr.first.symbol().qubit() > c)) break;
            if (tr.first.is_internal() && tr.first.symbol().qubit() == c) {
                auto in_outs = tr.second;
                for (const auto &in_out : in_outs) {
                    assert(in_out.first.size() == 2);
                    if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
                        tr.second[{in_out.first[0], in_out.first[1]+stateNum}] = in_out.second;
                        tr.second.erase(in_out.first);
                    }
                }
            }
        }
        stateNum += aut2.stateNum;
        remove_useless();
        reduce();
    } else {
        exit(1);
        // this->semi_determinize();
        // auto aut1 = *this;
        // aut1.branch_restriction(c, false);
        // auto aut2 = *this;
        // aut2.branch_restriction(c2, false);
        // auto aut3 = aut2;
        // aut3.branch_restriction(c, false);
        // auto aut4 = *this;
        // aut4.branch_restriction(c, true);
        // aut4.branch_restriction(c2, true);
        // auto aut5 = aut4;
        // aut4.value_restriction(t, false);
        // aut4.branch_restriction(t, true);
        // aut5.value_restriction(t, true);
        // aut5.branch_restriction(t, false);
        // *this = aut1 + aut2 - aut3 + aut4 + aut5;
        // this->semi_undeterminize();
    }
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "Toffoli" << c << "," << c2 << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Tdg(int t) {
    // #ifdef TO_QASM
    //     system(("echo 'tdg qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
    //     return;
    // #endif
    auto start = std::chrono::steady_clock::now();
    auto aut2 = *this;
    TransitionMap transitions_new;
    for (const auto &t_old : aut2.transitions) {
        const SymbolTag &symbol_tag = t_old.first;
        if (symbol_tag.is_leaf()) {
            SymbolTag s = symbol_tag;
            s.symbol().degree45cw();
            transitions_new[s] = t_old.second;
        } else {
            // assert(symbol_tag.tag().size() <= 1);
            transitions_new.insert(t_old);
        }
    }
    aut2.transitions = transitions_new;
    /******************************/
    for (const auto &tr : aut2.transitions) {
        const SymbolTag &symbol_tag = tr.first;
        if (!(symbol_tag.is_internal() && symbol_tag.symbol().qubit() <= t)) {
            auto &ttf = transitions[symbol_tag];
            for (const auto &in_out : tr.second) {
                StateVector in;
                for (const auto &s : in_out.first)
                    in.push_back(s+stateNum);
                for (const auto &s : in_out.second)
                    ttf[in].insert(s+stateNum);
            }
        }
    }
    for (auto &tr : transitions) {
        if (tr.first.is_leaf() || (tr.first.is_internal() && tr.first.symbol().qubit() > t)) break;
        if (tr.first.is_internal() && tr.first.symbol().qubit() == t) {
            auto in_outs = tr.second;
            for (const auto &in_out : in_outs) {
                assert(in_out.first.size() == 2);
                if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
                    tr.second[{in_out.first[0], in_out.first[1]+stateNum}] = in_out.second;
                    tr.second.erase(in_out.first);
                }
            }
        }
    }
    stateNum += aut2.stateNum;
    remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "Tdg" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Sdg(int t) {
    // #ifdef TO_QASM
    //     system(("echo 'sdg qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
    //     return;
    // #endif
    auto start = std::chrono::steady_clock::now();
    auto aut2 = *this;
    TransitionMap transitions_new;
    for (const auto &t_old : aut2.transitions) {
        const SymbolTag &symbol_tag = t_old.first;
        if (symbol_tag.is_leaf()) {
            SymbolTag s = symbol_tag;
            s.symbol().degree90cw();
            transitions_new[s] = t_old.second;
        } else {
            // assert(symbol_tag.tag().size() <= 1);
            transitions_new.insert(t_old);
        }
    }
    aut2.transitions = transitions_new;
    /******************************/
    for (const auto &tr : aut2.transitions) {
        const SymbolTag &symbol_tag = tr.first;
        if (!(symbol_tag.is_internal() && symbol_tag.symbol().qubit() <= t)) {
            auto &ttf = transitions[symbol_tag];
            for (const auto &in_out : tr.second) {
                StateVector in;
                for (const auto &s : in_out.first)
                    in.push_back(s+stateNum);
                for (const auto &s : in_out.second)
                    ttf[in].insert(s+stateNum);
            }
        }
    }
    for (auto &tr : transitions) {
        if (tr.first.is_leaf() || (tr.first.is_internal() && tr.first.symbol().qubit() > t)) break;
        if (tr.first.is_internal() && tr.first.symbol().qubit() == t) {
            auto in_outs = tr.second;
            for (const auto &in_out : in_outs) {
                assert(in_out.first.size() == 2);
                if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
                    tr.second[{in_out.first[0], in_out.first[1]+stateNum}] = in_out.second;
                    tr.second.erase(in_out.first);
                }
            }
        }
    }
    stateNum += aut2.stateNum;
    remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "Sdg" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::swap(int t1, int t2) {
    // #ifdef TO_QASM
    //     system(("echo 'swap qubits[" + std::to_string(t1-1) + "], qubits[" + std::to_string(t2-1) + "];' >> " + QASM_FILENAME).c_str());
    //     return;
    // #endif
    auto start = std::chrono::steady_clock::now();
    CNOT(t1, t2); gateCount--; // prevent repeated counting
    CNOT(t2, t1); gateCount--; // prevent repeated counting
    CNOT(t1, t2); gateCount--; // prevent repeated counting
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
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
        case 6: Rx(a); break;
        case 7: Ry(a); break;
        case 8: CNOT(a, b); break;
        case 9: CZ(a, b); break;
        case 10: Toffoli(a, b, c); break;
        // case 11: Fredkin(a, b, c); break;
        default: break;
    }
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;