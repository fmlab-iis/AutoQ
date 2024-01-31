#include <autoq/aut_description.hh>
#include <autoq/complex/complex.hh>

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
void AUTOQ::Automata<Symbol>::X(int t) {
    #ifdef TO_QASM
        system(("echo 'x qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    auto transitions_copy = transitions;
    for (const auto &tr : transitions_copy) {
        const auto &symbol_tag = tr.first;
        if (symbol_tag.is_internal() && symbol_tag.symbol().qubit() == t) {
            for (const auto &out_ins : tr.second) {
                const auto &q = out_ins.first;
                transitions[symbol_tag].erase(q);
                for (const auto &in : out_ins.second) {
                    assert(in.size() == 2);
                    transitions[symbol_tag][q].insert({in[1], in[0]});
                }
            }
        }
    }
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "X" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Y(int t) {
    #ifdef TO_QASM
        system(("echo 'y qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    TransitionMap transitions_copy = transitions;
    for (const auto &tr : transitions_copy) {
        SymbolTag symbol_tag = tr.first;
        if (symbol_tag.is_leaf())
            symbol_tag.symbol().negate();
        if (!(symbol_tag.is_internal() && symbol_tag.symbol().qubit() <= t)) {
            for (const auto &out_ins : tr.second) {
                const auto &q = out_ins.first + stateNum;
                for (auto in : out_ins.second) {
                    for (unsigned i=0; i<in.size(); i++)
                        in.at(i) += stateNum;
                    transitions[symbol_tag][q].insert(in);
                }
            }
        }
    }
    for (auto &tr : transitions) {
        if (tr.first.is_leaf() || (tr.first.is_internal() && tr.first.symbol().qubit() > t)) break;
        if (tr.first.is_internal() && tr.first.symbol().qubit() == t) {
            for (auto &out_ins : tr.second) {
                std::vector<StateVector> vec(out_ins.second.begin(), out_ins.second.end());
                for (auto &in : vec) {
                    assert(in.size() == 2);
                    if (in.at(0) < stateNum && in.at(1) < stateNum) {
                        std::swap(in.at(0), in.at(1));
                        in.at(0) += stateNum;
                        // out_ins.second.erase(in);
                        // out_ins.second.insert({in.at(1)+stateNum, in.at(0)});
                    }
                }
                out_ins.second = std::set<StateVector>(vec.begin(), vec.end());
            }
        }
    }
    stateNum *= 2;
    omega_multiplication(2);
    remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "Y" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Z(int t, bool opt) {
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
            for (const auto &out_ins : tr.second) {
                const auto &q = out_ins.first + stateNum;
                auto &tsq = transitions[symbol_tag][q];
                for (auto in : out_ins.second) {
                    for (auto &e : in)
                        e += stateNum;
                    tsq.insert(in);
                }
            }
        }
    }
    for (auto &tr : transitions) {
        if (tr.first.is_leaf() || (tr.first.is_internal() && tr.first.symbol().qubit() > t)) break;
        if (tr.first.is_internal() && tr.first.symbol().qubit() == t) {
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
    stateNum *= 2;
    if (opt) {
        remove_useless();
        reduce();
    }
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "Z" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

// template <typename Symbol>
// void AUTOQ::Automata<Symbol>::General_Single_Qubit_Gate(int t, const AUTOQ::Complex::Complex &a, const AUTOQ::Complex::Complex &b, const AUTOQ::Complex::Complex &c, const AUTOQ::Complex::Complex &d) {
//     this->semi_determinize();
//     auto aut1 = *this;
//     aut1.branch_restriction(t, false);
//     auto aut2 = *this;
//     aut2.value_restriction(t, true);
//     aut2.branch_restriction(t, false);
//     auto autL = aut1 * a + aut2 * b;
//     auto aut3 = *this;
//     aut3.value_restriction(t, false);
//     aut3.branch_restriction(t, true);
//     auto aut4 = *this;
//     aut4.branch_restriction(t, true);
//     auto autR = aut3 * c + aut4 * d;
//     *this = autL + autR;
//     this->semi_undeterminize();
// }

template <typename Symbol>
void AUTOQ::Automata<Symbol>::H(int t) {
    #ifdef TO_QASM
        system(("echo 'h qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    this->semi_determinize();
    auto aut1 = *this;
    aut1.value_restriction(t, false);
    auto aut2 = *this;
    aut2.value_restriction(t, true);
    aut2.branch_restriction(t, false);
    auto aut3 = *this;
    aut3.branch_restriction(t, true);
    *this = aut1 + aut2 - aut3;
    divide_by_the_square_root_of_two();
    this->semi_undeterminize();
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
        if (tr.first.is_leaf() || (tr.first.is_internal() && tr.first.symbol().qubit() > t)) break;
        if (tr.first.is_internal() && tr.first.symbol().qubit() == t) {
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
        if (tr.first.is_leaf() || (tr.first.is_internal() && tr.first.symbol().qubit() > t)) break;
        if (tr.first.is_internal() && tr.first.symbol().qubit() == t) {
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
    this->semi_determinize();
    auto aut1 = *this;
    auto aut2 = *this;
    aut2.value_restriction(t, false);
    aut2.branch_restriction(t, true);
    auto aut3 = *this;
    aut3.value_restriction(t, true);
    aut3.branch_restriction(t, false);
    aut2 = aut2 + aut3;
    aut2.omega_multiplication(2);
    *this = aut1 - aut2;
    divide_by_the_square_root_of_two();
    this->semi_undeterminize();
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
    this->semi_determinize();
    auto aut1 = *this;
    aut1.value_restriction(t, false);
    auto aut2 = *this;
    aut2.branch_restriction(t, true);
    auto aut3 = *this;
    aut3.value_restriction(t, true);
    aut3.branch_restriction(t, false);
    *this = aut1 + aut2 - aut3;
    divide_by_the_square_root_of_two();
    this->semi_undeterminize();
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
        this->semi_determinize();
        auto aut1 = *this;
        aut1.branch_restriction(c, false);
        auto aut2 = *this;
        aut2.branch_restriction(c, true);
        auto aut3 = aut2;
        aut2.value_restriction(t, false);
        aut2.branch_restriction(t, true);
        aut3.value_restriction(t, true);
        aut3.branch_restriction(t, false);
        *this = aut1 + aut2 + aut3;
        this->semi_undeterminize();
    } else {
        auto aut2 = *this;
        aut2.X(t); gateCount--; // prevent repeated counting
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
    aut2.Z(t, false); gateCount--; // prevent repeated counting
    for (const auto &tr : aut2.transitions) {
        const SymbolTag &symbol_tag = tr.first;
        if (!(symbol_tag.is_internal() && symbol_tag.symbol().qubit() <= c)) {
            auto &ttf = transitions[symbol_tag];
            for (const auto &out_ins : tr.second) {
                const auto &q = out_ins.first + stateNum;
                for (auto in : out_ins.second) {
                    for (auto &e : in)
                        e += stateNum;
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
        reduce();
    } else {
        this->semi_determinize();
        auto aut1 = *this;
        aut1.branch_restriction(c, false);
        auto aut2 = *this;
        aut2.branch_restriction(c2, false);
        auto aut3 = aut2;
        aut3.branch_restriction(c, false);
        auto aut4 = *this;
        aut4.branch_restriction(c, true);
        aut4.branch_restriction(c2, true);
        auto aut5 = aut4;
        aut4.value_restriction(t, false);
        aut4.branch_restriction(t, true);
        aut5.value_restriction(t, true);
        aut5.branch_restriction(t, false);
        *this = aut1 + aut2 - aut3 + aut4 + aut5;
        this->semi_undeterminize();
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
            assert(symbol_tag.tag().size() <= 1);
            transitions_new.insert(t_old);
        }
    }
    aut2.transitions = transitions_new;
    /******************************/
    for (const auto &tr : aut2.transitions) {
        const SymbolTag &symbol_tag = tr.first;
        if (!(symbol_tag.is_internal() && symbol_tag.symbol().qubit() <= t)) {
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
        if (tr.first.is_leaf() || (tr.first.is_internal() && tr.first.symbol().qubit() > t)) break;
        if (tr.first.is_internal() && tr.first.symbol().qubit() == t) {
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
            assert(symbol_tag.tag().size() <= 1);
            transitions_new.insert(t_old);
        }
    }
    aut2.transitions = transitions_new;
    /******************************/
    for (const auto &tr : aut2.transitions) {
        const SymbolTag &symbol_tag = tr.first;
        if (!(symbol_tag.is_internal() && symbol_tag.symbol().qubit() <= t)) {
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
        if (tr.first.is_leaf() || (tr.first.is_internal() && tr.first.symbol().qubit() > t)) break;
        if (tr.first.is_internal() && tr.first.symbol().qubit() == t) {
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

template <typename Symbol>
void AUTOQ::Automata<Symbol>::CK(int c, int t) {
    #ifdef TO_QASM
        system(("echo 'cu qubits[" + std::to_string(c-1) + "], qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    this->semi_determinize();

    auto aut1 = *this;
    aut1.branch_restriction(t, false);
    auto aut2 = *this;
    aut2.value_restriction(t, true);
    aut2.branch_restriction(t, false);
    auto autL = aut1 * 21 + aut2 * -220;
    auto aut3 = *this;
    aut3.value_restriction(t, false);
    aut3.branch_restriction(t, true);
    auto aut4 = *this;
    aut4.branch_restriction(t, true);
    auto autR = aut3 * 220 + aut4 * 21;
    autR = autL + autR; // hide the denominator 221
    autR.branch_restriction(c, true);

    autL = *this;
    autL.branch_restriction(c, false);
    autL = autL * 221;

    *this = autL + autR;
    this->semi_undeterminize();
    remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "CU" << c << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

template <typename Symbol>
AUTOQ::Automata<Symbol> AUTOQ::Automata<Symbol>::measure(int t, bool outcome) const {
    #ifdef TO_QASM
        system(("echo 'measure qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    auto aut = *this;
    for (auto &tr : aut.transitions) {
        if (tr.first.is_internal()) {
            if (tr.first.symbol().qubit() == t) {
                for (auto &out_ins : tr.second) {
                    std::vector<StateVector> vec(out_ins.second.begin(), out_ins.second.end());
                    for (auto &in : vec) {
                        assert(in.size() == 2);
                        assert(in.at(0) < aut.stateNum && in.at(1) < aut.stateNum);
                        if (!outcome) { // connect the "true" branch to "zero"
                            in.at(1) = aut.stateNum;
                        } else { // connect the "false" branch to "zero"
                            in.at(0) = aut.stateNum;
                        }
                    }
                    out_ins.second = std::set<StateVector>(vec.begin(), vec.end());
                }
                aut.stateNum++;
            }
        }
    }
    for (unsigned i=t+1; i<=aut.qubitNum; i++) {
        aut.transitions[{i}][aut.stateNum-1].insert({aut.stateNum, aut.stateNum});
        aut.stateNum++;
    }
    aut.transitions[Symbol()][aut.stateNum-1].insert({{}});
    aut.remove_useless();
    aut.reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "measure " << t << "：" << aut.stateNum << " states " << aut.count_transitions() << " transitions " << toString(duration) << "\n";
    return aut;
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