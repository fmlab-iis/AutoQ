#include <vata/util/aut_description.hh>

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
}

int VATA::Util::TreeAutomata::count_transitions() {
    int count = 0;
    for (const auto &t : transitions)
        for (const auto &in_outs : t.second) {
            count += in_outs.second.size();
        }
    return count;
}

void VATA::Util::TreeAutomata::X(int k) {
    auto start = std::chrono::steady_clock::now();
    auto transitions_copy = transitions;
    for (const auto &t : transitions_copy) {
        if (is_internal(t.first) && t.first[0] == k) {
            transitions.erase(t.first);
            for (const auto &in_out : t.second) {
                assert(in_out.first.size() == 2);
                transitions[t.first][{in_out.first[1], in_out.first[0]}] = in_out.second;
            }
        }
    }
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "X" << k << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

void VATA::Util::TreeAutomata::Y(int k) {
    auto start = std::chrono::steady_clock::now();
    TransitionMap transitions_copy = transitions;
    for (const auto &t : transitions_copy) {
        Symbol symbol;
        if (is_leaf(t.first)) {
            symbol = Symbol({-t.first[0], -t.first[1], -t.first[2], -t.first[3], t.first[4]});
        } else {
            symbol = t.first;
        }
        if (!(is_internal(symbol) && symbol[0] <= k)) {
            for (const auto &in_out : t.second) {
                StateVector in;
                for (const auto &s : in_out.first)
                    in.push_back(s+stateNum);
                for (const auto &s : in_out.second)
                    transitions[symbol][in].insert(s+stateNum);
            }
        }
    } 
    auto &tak = transitions.at({k});
    auto in_outs = tak;
    for (const auto &in_out : in_outs) {
        assert(in_out.first.size() == 2);
        if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
            tak[{in_out.first[1]+stateNum, in_out.first[0]}] = in_out.second;
            tak.erase(in_out.first);
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

void VATA::Util::TreeAutomata::Z(int t) {
    auto start = std::chrono::steady_clock::now();
    TransitionMap transitions_copy = transitions;
    for (const auto &tr : transitions_copy) {
        Symbol symbol;
        if (is_leaf(tr.first)) {
            symbol = Symbol({-tr.first[0], -tr.first[1], -tr.first[2], -tr.first[3], tr.first[4]});
        } else {
            symbol = tr.first;
        }
        if (!(is_internal(symbol) && symbol[0] <= t)) {
            for (const auto &in_out : tr.second) {
                StateVector in;
                for (const auto &s : in_out.first)
                    in.push_back(s+stateNum);
                for (const auto &s : in_out.second)
                    transitions[symbol][in].insert(s+stateNum);
            }
        }
    } 
    auto &tak = transitions.at({t});
    auto in_outs = tak;
    for (const auto &in_out : in_outs) {
        assert(in_out.first.size() == 2);
        if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
            tak[{in_out.first[0], in_out.first[1]+stateNum}] = in_out.second;
            tak.erase(in_out.first);
        }
    }
    stateNum *= 2;
    remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "Z" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

void VATA::Util::TreeAutomata::H(int t) {
    auto start = std::chrono::steady_clock::now();
    this->semi_determinize();
    TreeAutomata aut1 = *this;
    aut1.value_restriction(t, false);
    TreeAutomata aut2 = *this;
    aut2.value_restriction(t, true);
    aut2.branch_restriction(t, false);
    TreeAutomata aut3 = *this;
    aut3.branch_restriction(t, true);
    *this = aut1 + aut2 - aut3;
    divide_by_the_square_root_of_two();
    this->semi_undeterminize();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "H" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

void VATA::Util::TreeAutomata::S(int t) {
    auto start = std::chrono::steady_clock::now();
    auto aut2 = *this;
    aut2.omega_multiplication(2);
    for (const auto &tr : aut2.transitions) {
        if (!(is_internal(tr.first) && tr.first[0] <= t)) {
            auto &ttf = transitions[tr.first];
            for (const auto &in_out : tr.second) {
                StateVector in;
                for (const auto &s : in_out.first)
                    in.push_back(s+stateNum);
                for (const auto &s : in_out.second)
                    ttf[in].insert(s+stateNum);
            }
        }
    }
    auto &tac = transitions.at({t});
    auto in_outs = tac;
    for (const auto &in_out : in_outs) {
        assert(in_out.first.size() == 2);
        if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
            tac[{in_out.first[0], in_out.first[1]+stateNum}] = in_out.second;
            tac.erase(in_out.first);
        }
    }
    stateNum += aut2.stateNum;
    remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "S" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

void VATA::Util::TreeAutomata::T(int t) {
    auto start = std::chrono::steady_clock::now();
    auto aut2 = *this;
    aut2.omega_multiplication();
    for (const auto &tr : aut2.transitions) {
        if (!(is_internal(tr.first) && tr.first[0] <= t)) {
            auto &ttf = transitions[tr.first];
            for (const auto &in_out : tr.second) {
                StateVector in;
                for (const auto &s : in_out.first)
                    in.push_back(s+stateNum);
                for (const auto &s : in_out.second)
                    ttf[in].insert(s+stateNum);
            }
        }
    }
    auto &tac = transitions.at({t});
    auto in_outs = tac;
    for (const auto &in_out : in_outs) {
        assert(in_out.first.size() == 2);
        if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
            tac[{in_out.first[0], in_out.first[1]+stateNum}] = in_out.second;
            tac.erase(in_out.first);
        }
    }
    stateNum += aut2.stateNum;
    remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "T" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

void VATA::Util::TreeAutomata::Rx(int t) {
    auto start = std::chrono::steady_clock::now();
    this->semi_determinize();
    TreeAutomata aut1 = *this;
    TreeAutomata aut2 = *this;
    aut2.value_restriction(t, false);
    aut2.branch_restriction(t, true);
    TreeAutomata aut3 = *this;
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

void VATA::Util::TreeAutomata::Ry(int t) {
    auto start = std::chrono::steady_clock::now();
    this->semi_determinize();
    TreeAutomata aut1 = *this;
    aut1.value_restriction(t, false);
    TreeAutomata aut2 = *this;
    aut2.branch_restriction(t, true);
    TreeAutomata aut3 = *this;
    aut3.value_restriction(t, true);
    aut3.branch_restriction(t, false);
    *this = aut1 + aut2 - aut3;
    divide_by_the_square_root_of_two();
    this->semi_undeterminize();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "Ry" << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

void VATA::Util::TreeAutomata::CNOT(int c, int t, bool opt) {
    auto start = std::chrono::steady_clock::now();
    assert(c != t);
    if (c > t) {
        this->semi_determinize();
        TreeAutomata aut1 = *this;
        aut1.branch_restriction(c, false);
        TreeAutomata aut2 = *this;
        aut2.branch_restriction(c, true);
        TreeAutomata aut3 = aut2;
        aut2.value_restriction(t, false);
        aut2.branch_restriction(t, true);
        aut3.value_restriction(t, true);
        aut3.branch_restriction(t, false);
        *this = aut1 + aut2 + aut3;
        this->semi_undeterminize();
    } else {
        auto aut2 = *this;
        aut2.X(t);
        for (const auto &tr : aut2.transitions) {
            if (!(is_internal(tr.first) && tr.first[0] <= c)) {
                auto &ttf = transitions[tr.first];
                for (const auto &in_out : tr.second) {
                    StateVector in;
                    for (const auto &s : in_out.first)
                        in.push_back(s+stateNum);
                    for (const auto &s : in_out.second)
                        ttf[in].insert(s+stateNum);
                }
            }
        }
        auto &tac = transitions.at({c});
        auto in_outs = tac;
        for (const auto &in_out : in_outs) {
            assert(in_out.first.size() == 2);
            if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
                tac[{in_out.first[0], in_out.first[1]+stateNum}] = in_out.second;
                tac.erase(in_out.first);
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

void VATA::Util::TreeAutomata::CZ(int c, int t) {
    auto start = std::chrono::steady_clock::now();
    assert(c != t);
    if (c > t) std::swap(c, t);
    auto aut2 = *this;
    for (const auto &tr : transitions) {
        Symbol symbol;
        if (is_leaf(tr.first)) {
            symbol = Symbol({-tr.first[0], -tr.first[1], -tr.first[2], -tr.first[3], tr.first[4]});
        } else {
            symbol = tr.first;
        }
        if (!(is_internal(symbol) && symbol[0] <= t)) {
            for (const auto &in_out : tr.second) {
                StateVector in;
                for (const auto &s : in_out.first)
                    in.push_back(s+stateNum);
                for (const auto &s : in_out.second)
                    aut2.transitions[symbol][in].insert(s+stateNum);
            }
        }
    } 
    auto &tak = aut2.transitions.at({t});
    auto in_outs = tak;
    for (const auto &in_out : in_outs) {
        assert(in_out.first.size() == 2);
        if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
            tak[{in_out.first[0], in_out.first[1]+stateNum}] = in_out.second;
            tak.erase(in_out.first);
        }
    }
    for (const auto &tr : aut2.transitions) {
        if (!(is_internal(tr.first) && tr.first[0] <= c)) {
            for (const auto &in_out : tr.second) {
                StateVector in;
                for (const auto &s : in_out.first)
                    in.push_back(s+stateNum);
                for (const auto &s : in_out.second)
                    transitions[tr.first][in].insert(s+stateNum);
            }
        }
    } 
    auto &tak2 = transitions.at({c});
    auto in_outs2 = tak2;
    for (const auto &in_out : in_outs2) {
        assert(in_out.first.size() == 2);
        if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
            tak2[{in_out.first[0], in_out.first[1]+stateNum}] = in_out.second;
            tak2.erase(in_out.first);
        }
    }
    stateNum *= 3;
    remove_useless();
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "CZ" << c << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << toString(duration) << "\n";
}

void VATA::Util::TreeAutomata::Toffoli(int c, int c2, int t) {
    auto start = std::chrono::steady_clock::now();
    assert(c != c2 && c2 != t && t != c);
    if (c < t && c2 < t) {
        if (c > c2) std::swap(c, c2);
        auto aut2 = *this;
        aut2.CNOT(c2, t, false);
        for (const auto &tr : aut2.transitions) {
            if (!(is_internal(tr.first) && tr.first[0] <= c)) {
                auto &ttf = transitions[tr.first];
                for (const auto &in_out : tr.second) {
                    StateVector in;
                    for (const auto &s : in_out.first)
                        in.push_back(s+stateNum);
                    for (const auto &s : in_out.second)
                        ttf[in].insert(s+stateNum);
                }
            }
        }
        auto &tac = transitions.at({c});
        auto in_outs = tac;
        for (const auto &in_out : in_outs) {
            assert(in_out.first.size() == 2);
            if (in_out.first[0] < stateNum && in_out.first[1] < stateNum) {
                tac[{in_out.first[0], in_out.first[1]+stateNum}] = in_out.second;
                tac.erase(in_out.first);
            }
        }
        stateNum += aut2.stateNum;
        remove_useless();
        reduce();
    } else {
        this->semi_determinize();
        TreeAutomata aut1 = *this;
        aut1.branch_restriction(c, false);
        TreeAutomata aut2 = *this;
        aut2.branch_restriction(c2, false);
        TreeAutomata aut3 = aut2;
        aut3.branch_restriction(c, false);
        TreeAutomata aut4 = *this;
        aut4.branch_restriction(c, true);
        aut4.branch_restriction(c2, true);
        TreeAutomata aut5 = aut4;
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

// void VATA::Util::TreeAutomata::Fredkin(int c, int t, int t2) {
//     auto start = std::chrono::steady_clock::now();
//     assert(c != t && t != t2 && t2 != c);
//     this->semi_determinize();
//     TreeAutomata aut1 = *this;
//     aut1.branch_restriction(c, false);
//     TreeAutomata aut2 = *this;
//     aut2.branch_restriction(c, true);
//     TreeAutomata aut3 = aut2;
//     TreeAutomata aut4 = aut2;
//     TreeAutomata aut5 = aut2;
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

void VATA::Util::TreeAutomata::randG(int G, int A, int B, int C) {
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