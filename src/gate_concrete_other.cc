/** Concrete other: Tdg, Sdg, Swap, CX(), Phase, CK, randG, measure. */
#include "autoq/aut_description.hh"
#include "autoq/util/util.hh"
#include "gate_macros.hh"
#include <boost/rational.hpp>
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wold-style-cast"
#include <boost/multiprecision/cpp_int.hpp>
#pragma GCC diagnostic pop


// --- Concrete other: Tdg, Sdg, Swap, Phase, CK, randG ---
template <typename Symbol>
void AUTOQ::Automata<Symbol>::Tdg(int t) {
    run_diagonal_concrete_gate(t, "Tdg", "tdg",
        [](Symbol*) {},
        std::bind(&Symbol::degree45cw, std::placeholders::_1),
        true);
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Sdg(int t) {
    run_diagonal_concrete_gate(t, "Sdg", "sdg",
        [](Symbol*) {},
        std::bind(&Symbol::degree90cw, std::placeholders::_1),
        true);
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
    // if (gateLog) std::cout << "Phase" << c << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::Convert::ToString(duration) << "\n";
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::CK(int c, int t) {
    #ifdef TO_QASM
        system(("echo 'ck qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    general_controlled_gate(c, t,
        [](const Symbol &l, const Symbol &r) -> Symbol { return l * 220 - r * 21; },
        [](const Symbol &l, const Symbol &r) -> Symbol { return l * 21 + r * 220; },
        [](const Symbol &l) -> Symbol { return l * 221; });
    reduce();
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "CK" << c << "," << t << "：" << stateNum << " states " << count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

template <typename Symbol>
AUTOQ::Automata<Symbol> AUTOQ::Automata<Symbol>::measure(int t, bool outcome) const {
    #ifdef TO_QASM
        system(("echo 'measure qubits[" + std::to_string(t-1) + "];' >> " + QASM_FILENAME).c_str());
        return;
    #endif
    auto start = std::chrono::steady_clock::now();
    auto aut = *this;
    if (outcome)
        aut.diagonal_gate(t, std::bind(&Symbol::back_to_zero, std::placeholders::_1), [](Symbol*) {});
    else
        aut.diagonal_gate(t, [](Symbol*) {}, std::bind(&Symbol::back_to_zero, std::placeholders::_1));
    // if (opt) {
        // remove_useless();
        aut.reduce();
    // }
    gateCount++;
    auto duration = std::chrono::steady_clock::now() - start;
    if (gateLog) std::cout << "measure " << t << "：" << aut.stateNum << " states " << aut.count_transitions() << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
    return aut;
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

template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
