/** Concrete single-qubit gates: X, Y, Z, H, S, T, Rx, Ry, Rz. */
#include "autoq/aut_description.hh"
#include "autoq/util/util.hh"
#include "autoq/gate_helpers.hh"
#include "autoq/gate_macros.hh"
#include <boost/rational.hpp>
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wold-style-cast"
#include <boost/multiprecision/cpp_int.hpp>
#pragma GCC diagnostic pop

template <typename Symbol>
void AUTOQ::Automata<Symbol>::run_single_qubit_concrete_gate(int t, const char* log_name, const char* qasm_name,
    const std::function<Symbol(const Symbol&, const Symbol&)>& u1u2,
    const std::function<Symbol(const Symbol&, const Symbol&)>& u3u4) {
#ifdef TO_QASM
    (void)u1u2; (void)u3u4;
    system(("echo '" + std::string(qasm_name) + " qubits[" + std::to_string(t - 1) + "];' >> " + QASM_FILENAME).c_str());
    return;
#endif
    (void)qasm_name;
    auto start = std::chrono::steady_clock::now();
    general_single_qubit_gate(t, u1u2, u3u4);
    concrete_gate_finish(*this, log_name, t, start);
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::run_diagonal_concrete_gate(int t, const char* log_name, const char* qasm_name,
    const std::function<void(Symbol*)>& multiply_by_c0,
    const std::function<void(Symbol*)>& multiply_by_c1,
    bool do_reduce) {
#ifdef TO_QASM
    (void)multiply_by_c0; (void)multiply_by_c1;
    system(("echo '" + std::string(qasm_name) + " qubits[" + std::to_string(t - 1) + "];' >> " + QASM_FILENAME).c_str());
    return;
#endif
    (void)qasm_name;
    auto start = std::chrono::steady_clock::now();
    diagonal_gate(t, multiply_by_c0, multiply_by_c1);
    if (do_reduce) reduce();
    concrete_gate_finish(*this, log_name, t, start);
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::run_concrete_gate_with_body(int t, const char* log_name, const char* qasm_name,
    std::function<void()> body) {
#ifdef TO_QASM
    (void)body;
    system(("echo '" + std::string(qasm_name) + " qubits[" + std::to_string(t - 1) + "];' >> " + QASM_FILENAME).c_str());
    return;
#endif
    (void)qasm_name;
    auto start = std::chrono::steady_clock::now();
    body();
    concrete_gate_finish(*this, log_name, t, start);
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::X(int t) {
    run_concrete_gate_with_body(t, "X", "x", [this, t]() {
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
    });
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Y(int t) {
    run_concrete_gate_with_body(t, "Y", "y", [this, t]() {
        X(t);
        gateCount--;
        diagonal_gate(t, std::bind(&Symbol::degree90cw, std::placeholders::_1), std::bind(&Symbol::omega_multiplication, std::placeholders::_1, 2));
        reduce();
    });
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Z(int t, bool opt) {
    run_diagonal_concrete_gate(t, "Z", "z",
        [](Symbol*) {},
        std::bind(&Symbol::negate, std::placeholders::_1),
        opt);
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::H(int t) {
    run_single_qubit_concrete_gate(t, "H", "h",
        [](const Symbol &l, const Symbol &r) -> Symbol { return (l + r).divide_by_the_square_root_of_two(); },
        [](const Symbol &l, const Symbol &r) -> Symbol { return (l - r).divide_by_the_square_root_of_two(); });
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::S(int t) {
    run_diagonal_concrete_gate(t, "S", "s",
        [](Symbol*) {},
        std::bind(&Symbol::omega_multiplication, std::placeholders::_1, 2),
        true);
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::T(int t) {
    run_diagonal_concrete_gate(t, "T", "t",
        [](Symbol*) {},
        std::bind(&Symbol::omega_multiplication, std::placeholders::_1, 1),
        true);
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Rx(const boost::rational<boost::multiprecision::cpp_int> &theta, int t) {
    run_single_qubit_concrete_gate(t, "Rx", "rx(...)",
        [theta](Symbol l, Symbol r) -> Symbol { return l.multiply_cos(theta/2) - r.multiply_isin(theta/2); },
        [theta](Symbol l, Symbol r) -> Symbol { return r.multiply_cos(theta/2) - l.multiply_isin(theta/2); });
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Ry(int t) {
    run_single_qubit_concrete_gate(t, "Ry", "ry(pi/2)",
        [](const Symbol &l, const Symbol &r) -> Symbol { return (l - r).divide_by_the_square_root_of_two(); },
        [](const Symbol &l, const Symbol &r) -> Symbol { return (l + r).divide_by_the_square_root_of_two(); });
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::Rz(const boost::rational<boost::multiprecision::cpp_int> &theta, int t) {
    run_diagonal_concrete_gate(t, "Rz", "rz(...)",
        std::bind(&Symbol::counterclockwise, std::placeholders::_1, -theta / 2),
        std::bind(&Symbol::counterclockwise, std::placeholders::_1, theta / 2),
        true);
}

template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
