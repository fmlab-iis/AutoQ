#include <fstream>
#include <iostream>
#include <autoq/parsing/timbuk_parser.hh>
#include <autoq/serialization/timbuk_serializer.hh>
#include <autoq/aut_description.hh>
#include <autoq/inclusion.hh>
#include <autoq/util/util.hh>
#include <util_sim.h>
#include <sys/wait.h>
#include <unistd.h>

#include <chrono>
#include <iomanip>
#include <regex>

using namespace std;
using AUTOQ::TreeAutomata;
using AUTOQ::Util::ShellCmd;
using AUTOQ::Util::ReadFile;

int type, n;

int rand_gen();
void rand_gen(int &a, int &b);
void rand_gen(int &a, int &b, int &c);
std::string toString(std::chrono::steady_clock::duration tp);

int main(int argc, char **argv) {
try {
    if (argc < 3 || (argc >= 2 && ((strcmp(argv[1], "-h")==0) || (strcmp(argv[1], "--help")==0)))) {
        std::cout << R"(usage: ./autoq [-h] pre.{aut|hsl} circuit.qasm [spec.{aut|hsl}] [constraint.smt]

positional arguments:
  pre.{aut|hsl}         the input automaton

                        The extension "aut" implies the Timbuk format of tree automata.
                        The extension "hsl" implies the high-level specification language.

  circuit.qasm          the quantum circuit in OpenQASM 2.0.

  spec.{aut|hsl}        the specification automaton we expect to include the output automaton produced by
                        the input automaton passing through the circuit
                        This file can be omitted when the probability amplitudes are all concrete. In this
                        case, the program only prints the output automaton without checking inclusion.

                        The extension "aut" implies the Timbuk format of tree automata.
                        The extension "hsl" implies the high-level specification language.

  constraint.smt        the SMT-LIB file declaring all variables used in the automaton and their constraints
                        This file is required when the verification is performed under the symbolic mode.


optional arguments:
  -h, --help            show this help message and exit)" << std::endl;
        return 0;
    }

    if (argc < 5) {
        if (argc >= 4) { // Check VATA_PATH first!
            if (std::getenv("VATA_PATH") == nullptr) {
                throw std::runtime_error("[ERROR] The environment variable VATA_PATH is not found!");
            }
        }

        std::string automaton;
        std::string constraint; // The following template argument does not matter.
        if (AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::findAndSplitSubstring(argv[1], automaton, constraint)) {
            auto startVer = chrono::steady_clock::now();
            AUTOQ::SymbolicAutomata aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ParseString(automaton);
            aut.execute(argv[2]);
            // aut.fraction_simplification();
            aut.reduce();
            AUTOQ::PredicateAutomata spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>::FromFileToAutomata(argv[3]);
            AUTOQ::Constraint C(constraint.c_str());
            std::cout << "OUTPUT AUTOMATON:\n";
            std::cout << "=================\n";
            aut.print_aut();
            std::cout << "=================\n";
            std::cout << "-\n" << AUTOQ::is_spec_satisfied(C, aut, spec) << " " << toString(chrono::steady_clock::now() - startVer) << " " << getPeakRSS() / 1024 / 1024 << "MB\n";
        } else {
            AUTOQ::TreeAutomata aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::FromFileToAutomata(argv[1]);
            // int stateBefore = aut.stateNum, transitionBefore = aut.transition_size();
            auto startSim = chrono::steady_clock::now();
            aut.execute(argv[2]);
            auto durationSim = chrono::steady_clock::now() - startSim;
            auto durationVer = durationSim; // just borrow its type!
            // aut.fraction_simplification();
            auto startVer = chrono::steady_clock::now();
            std::cout << "OUTPUT AUTOMATON:\n";
            std::cout << "=================\n";
            aut.print_aut();
            std::cout << "=================\n";
            if (argc >= 4) {
                auto aut2 = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::FromFileToAutomata(argv[3]);
                if (!AUTOQ::TreeAutomata::check_inclusion(aut, aut2)) {
                    std::cout << "-\n0\n";
                    // throw std::runtime_error("Does not satisfy the postcondition!");
                    // std::cout << AUTOQ::Util::Convert::ToString(aut.qubitNum) << " & " << AUTOQ::TreeAutomata::gateCount
                    // << " & " << stateBefore << " & " << aut.stateNum
                    // << " & " << transitionBefore << " & " << aut.transition_size()
                    // << " & " << toString(durationSim) << " & V";
                } else
                    std::cout << "-\n1\n";
            } else {
                durationVer = chrono::steady_clock::now() - startVer;
                // std::cout << AUTOQ::Util::Convert::ToString(aut.qubitNum) << " & " << AUTOQ::TreeAutomata::gateCount
                //     << " & " << stateBefore << " & " << aut.stateNum
                //     << " & " << transitionBefore << " & " << aut.transition_size()
                //     << " & " << toString(durationSim) << " & " << toString(durationVer);
            }
        }
    } else { // argc >= 5
        auto startVer = chrono::steady_clock::now();
        AUTOQ::SymbolicAutomata aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::FromFileToAutomata(argv[1]);
        aut.execute(argv[2]);
        // aut.fraction_simplification();
        aut.reduce();
        AUTOQ::PredicateAutomata spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>::FromFileToAutomata(argv[3]);
        std::ifstream t(argv[4]);
        if (!t) // in case the file could not be open
            throw std::runtime_error("[ERROR] Failed to open file " + std::string(argv[4]) + ".");
        std::stringstream buffer;
        buffer << t.rdbuf();
        AUTOQ::Constraint C(buffer.str().c_str());
        std::cout << "OUTPUT AUTOMATON:\n";
        std::cout << "=================\n";
        aut.print_aut();
        std::cout << "=================\n";
        std::cout << "-\n" << AUTOQ::is_spec_satisfied(C, aut, spec) << " " << toString(chrono::steady_clock::now() - startVer) << " " << getPeakRSS() / 1024 / 1024 << "MB\n";
    }
    return 0;
} catch (std::exception &e) {
    std::cout << e.what() << std::endl;
    return 0;
}
}

int rand_gen() {
    if (type == 3) return 1;
    else if (type == 5) return n;
    else return rand() % n + 1;
}
void rand_gen(int &a, int &b) {
    if (type == 3) { // TOP
        a = 1;
        b = 2;
    } else if (type == 5) { // BOTTOM
        a = n-1;
        b = n;
    } else {
        a = rand() % n + 1;
        do {
            b = rand() % n + 1;
        } while (b == a);
    }
}
void rand_gen(int &a, int &b, int &c) {
    if (type == 3) { // TOP
        a = 1;
        b = 2;
        c = 3;
    } else if (type == 5) { // BOTTOM
        a = n-2;
        b = n-1;
        c = n;
    } else {
        a = rand() % n + 1;
        do {
            b = rand() % n + 1;
        } while (b == a);
        do {
            c = rand() % n + 1;
        } while (c == a || c == b);
    }
}

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
    if (d.count() > 0)
        ss << d.count() << 'd' << h.count() << 'h' << m.count() << 'm' << s.count() << 's';
    else if (h.count() > 0)
        ss << h.count() << 'h' << m.count() << 'm' << s.count() << 's';
    else if (m.count() == 0 && s.count() < 10) {
        ss << s.count() << '.' << ms.count() / 100 << "s";
    } else {
        if (m.count() > 0) ss << m.count() << 'm';
        ss << s.count() << 's';// << " & ";
    }
    ss.fill(fill);
    return ss.str();
}
