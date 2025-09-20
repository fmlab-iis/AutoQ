#include <fstream>
#include <iostream>
#include <autoq/error.hh>
#include <autoq/parsing/timbuk_parser.hh>
#include <autoq/parsing/complex_parser.hh>
#include <autoq/serialization/timbuk_serializer.hh>
#include <autoq/aut_description.hh>
#include <autoq/inclusion.hh>
#include <autoq/util/util.hh>
#include <autoq/util/string.hh>
#include <autoq/parsing/ExtendedDirac/EvaluationVisitor.h>
#include <autoq/complex/complex.hh>
#include <sys/wait.h>
#include <unistd.h>
#include <chrono>
#include <iomanip>
#include <regex>
#include <fenv.h>
#include <csignal>
#include <fenv_darwin.h>
#include <CLI11.hpp>
#include <version.h>

using namespace std;

int extract_qubit(const std::string& filename) {
    std::ifstream file(filename);
    if (!file.is_open()) {
        std::cerr << "Unable to open file" << std::endl;
        return -1; // Indicate an error opening the file
    }

    std::string line;
    std::regex pattern(R"(qreg\s+\w+\[(\d+)\];)");
    std::smatch match;
    while (std::getline(file, line)) {
        if (std::regex_search(line, match, pattern)) {
            return std::stoi(match[1].str());
        }
    }

    std::cerr << "Pattern not found" << std::endl;
    return -1; // Indicate that the pattern was not found
}

void adjust_N_in_nTuple(const std::string &filename) {
    if constexpr(!std::is_same_v<AUTOQ::Complex::Complex, AUTOQ::Complex::nTuple>) return;
    /************************************************************************************/
    std::ifstream qasm(filename);
    const std::regex digit("\\d+");
    const std::regex rx(R"(rx\((.+)\).+\[(\d+)\];)");
    const std::regex rz(R"(rz\((.+)\).+\[(\d+)\];)");
    const std::regex_iterator<std::string::iterator> END;
    if (!qasm.is_open()) THROW_AUTOQ_ERROR("Failed to open file " + std::string(filename) + ".");
    std::string line;
    while (getline(qasm, line)) {
        line = AUTOQ::String::trim(line);
        std::smatch match_rx; std::regex_search(line, match_rx, rx);
        std::smatch match_rz; std::regex_search(line, match_rz, rz);
        if (line.find("OPENQASM") == 0 || line.find("include ") == 0|| line.find("//") == 0) continue;
        if (line.find("qreg ") == 0) {
        } else if (line.find("x ") == 0) {
        } else if (line.find("y ") == 0) {
            if (AUTOQ::Complex::nTuple::N < 2) {
                AUTOQ::Complex::nTuple::N = 2;
            }
        } else if (line.find("z ") == 0) {
        } else if (line.find("h ") == 0) {
        } else if (line.find("s ") == 0) {
            if (AUTOQ::Complex::nTuple::N < 2) {
                AUTOQ::Complex::nTuple::N = 2;
            }
        } else if (line.find("sdg ") == 0) {
            if (AUTOQ::Complex::nTuple::N < 2) {
                AUTOQ::Complex::nTuple::N = 2;
            }
        } else if (line.find("t ") == 0) {
            if (AUTOQ::Complex::nTuple::N < 4) {
                AUTOQ::Complex::nTuple::N = 4;
            }
        } else if (line.find("tdg ") == 0) {
            if (AUTOQ::Complex::nTuple::N < 4) {
                AUTOQ::Complex::nTuple::N = 4;
            }
        } else if (match_rx.size() == 3) {
            std::string angle = match_rx[1];
            size_t pos = angle.find("pi");
            if (pos != std::string::npos) {
                angle.replace(pos, 2, "1");
            } else if (angle != "0") {
                THROW_AUTOQ_ERROR("The angle in rx gate is not a multiple of pi!");
            }
            auto theta = EvaluationVisitor<>::ComplexParser(angle).getComplex().to_rational() / 2;
            if (AUTOQ::Complex::nTuple::N < static_cast<decltype(AUTOQ::Complex::nTuple::N)>(theta.denominator())) {
                AUTOQ::Complex::nTuple::N = static_cast<decltype(AUTOQ::Complex::nTuple::N)>(theta.denominator());
            }
        } else if (match_rz.size() == 3) {
            std::string angle = match_rz[1];
            size_t pos = angle.find("pi");
            if (pos != std::string::npos) {
                angle.replace(pos, 2, "1");
            } else if (angle != "0") {
                THROW_AUTOQ_ERROR("The angle in rz gate is not a multiple of pi!");
            }
            auto theta = EvaluationVisitor<>::ComplexParser(angle).getComplex().to_rational() / 2;
            if (AUTOQ::Complex::nTuple::N < static_cast<decltype(AUTOQ::Complex::nTuple::N)>(theta.denominator())) {
                AUTOQ::Complex::nTuple::N = static_cast<decltype(AUTOQ::Complex::nTuple::N)>(theta.denominator());
            }
        } else if (line.find("ry(pi/2) ") == 0 || line.find("ry(pi / 2)") == 0) {
        } else if (line.find("cx ") == 0 || line.find("CX ") == 0 ) {
        } else if (line.find("cz ") == 0) {
        } else if (line.find("for ") == 0){
        } else if (line.find("}") == 0){
        } else if (line.find("ccx ") == 0) {
        } else if (line.find("swap ") == 0) {
        } else if (line.find("PRINT_STATS") == 0) {
        } else if (line.find("PRINT_AUT") == 0) {
        } else if (line.find("STOP") == 0) {
        }
        // } else if (line.length() > 0)
        //     THROW_AUTOQ_ERROR("unsupported gate: " + line + ".");
    }
    qasm.close();
    // AUTOQ_DEBUG(AUTOQ::Complex::nTuple::N);
}

AUTOQ::TreeAutomata aut;
AUTOQ::TreeAutomata aut2;
void timeout_handler(int) {
    std::map<std::string, std::string> stats;
    stats["gate"] = AUTOQ::Util::Convert::toString(AUTOQ::TreeAutomata::total_gate_time - AUTOQ::TreeAutomata::total_removeuseless_time - AUTOQ::TreeAutomata::total_reduce_time);
    stats["removeuseless"] = AUTOQ::Util::Convert::toString(AUTOQ::TreeAutomata::total_removeuseless_time);
    stats["reduce"] = AUTOQ::Util::Convert::toString(AUTOQ::TreeAutomata::total_reduce_time);
    stats["include"] = AUTOQ::Util::Convert::toString(AUTOQ::TreeAutomata::total_include_time);
    stats["total"] = "1800";
    stats["result"] = std::to_string(AUTOQ::TreeAutomata::gateCount);
    stats["aut1.trans"] = std::to_string(aut.count_transitions());
    stats["aut1.leaves"] = std::to_string(aut.count_leaves());
    stats["aut2.trans"] = std::to_string(aut2.count_transitions());
    stats["aut2.leaves"] = std::to_string(aut2.count_leaves());
    std::cout << AUTOQ::Util::Convert::ToString2(stats) << std::endl;
    exit(124); // Terminate the program
}

void set_timeout(unsigned int seconds) {
    // Register the signal handler
    signal(SIGALRM, timeout_handler);
    // Set an alarm for the specified number of seconds
    alarm(seconds);
}

int main(int argc, char **argv) {
try {
    // set_timeout(600);
    feenableexcept(FE_ALL_EXCEPT & ~FE_INEXACT);

    CLI::App app{"AutoQ 2.0: An automata-based C++ tool for quantum program verification."};
    std::string pre, circuit, post, circuit1, circuit2;

    bool summarize_loops = false;
    CLI::App* execution = app.add_subcommand("ex", "Execute a quantum circuit with a given precondition.");
    execution->add_option("pre.hsl", pre, "the precondition file")->required()->type_name("");
    execution->add_option("circuit.qasm", circuit, "the OpenQASM 2.0 or 3.0 circuit file")->required()->type_name("");
    execution->add_flag("--loopsum", summarize_loops, "Summarize loops using symbolic execution.");
    execution->callback([&]() {
        adjust_N_in_nTuple(circuit);
    });

    bool latex = false;
    CLI::App* verification = app.add_subcommand("ver", "Verify the execution result against a given postcondition.");
    verification->add_option("pre.hsl", pre, "the precondition file")->required()->type_name("");
    verification->add_option("circuit.qasm", circuit, "the OpenQASM 2.0 or 3.0 circuit file")->required()->type_name("");
    verification->add_option("post.hsl", post, "the postcondition file")->required()->type_name("");
    verification->add_flag("--loopsum", summarize_loops, "Summarize loops using symbolic execution.");
    verification->add_flag("-l,--latex", latex, "Print the statistics for tables in LaTeX.");
    verification->callback([&]() {
        adjust_N_in_nTuple(circuit);
    });

    CLI::App* equivalence_checking = app.add_subcommand("eq", "Check equivalence of two given quantum circuits.");
    equivalence_checking->add_option("circuit1.qasm", circuit1, "the OpenQASM 2.0 or 3.0 circuit file")->required()->type_name("");
    equivalence_checking->add_option("circuit2.qasm", circuit2, "the OpenQASM 2.0 or 3.0 circuit file")->required()->type_name("");
    equivalence_checking->add_flag("--loopsum", summarize_loops, "Summarize loops using symbolic execution.");
    equivalence_checking->add_flag("-l,--latex", latex, "Print the statistics for tables in LaTeX.");
    equivalence_checking->callback([&]() {
        adjust_N_in_nTuple(circuit1);
        adjust_N_in_nTuple(circuit2);
    });

    CLI::App* print = app.add_subcommand("print", "Print the set of quantum states.");
    print->add_option("states.hsl", pre, "the automaton file")->required()->type_name("");

    CLI::Option* version = app.add_flag("-v,--version", "Print the full Git commit hash ID.");

    // bool short_time = false, long_time = false;
    // app.add_flag("-t", short_time, "print times");
    // app.add_flag("--time", long_time, "print times");
    CLI11_PARSE(app, argc, argv); // Parse the command-line arguments

    if (*version) {
        std::cout << AUTOQ_GIT_SHA << std::endl;
        return 0;
    }

    auto start = chrono::steady_clock::now();
    // bool runConcrete; // or runSymbolic
    ParameterMap params;
    params["loop"] = "manual"; // set the default option for loop execution
    if(summarize_loops){
        // summarization of loops enabled
        params["loop"] = "symbolic";
    }
    if (execution->parsed()) {
        // runConcrete = true;
        auto aut1 = ReadAutomaton(pre);
        if constexpr (std::is_same_v<std::decay_t<decltype(aut1)>, AUTOQ::PredicateAutomata>) {
            THROW_AUTOQ_ERROR("Predicate amplitudes cannot be used in a precondition.");
        }
        if (std::holds_alternative<AUTOQ::SymbolicAutomata>(aut1) || AUTOQ::SymbolicAutomata::check_the_invariants_types(circuit) == "Symbolic") {
            auto [autVec, qp] = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadTwoAutomata(pre, pre, circuit);
            auto aut = autVec.at(0);
            autVec.erase(autVec.begin(), autVec.begin() + 2); // remove the first element
            bool verify = aut.execute(circuit, qp, autVec, params);
            if (!autVec.empty()) {
                if (verify) std::cout << "[OK] The circuit execution satisfies the loop invariant." << std::endl;
                else std::cout << "[ERROR] The circuit execution violates the loop invariant." << std::endl;
            }
            aut.print_language("OUTPUT:\n");
        } else {
            auto [autVec, qp] = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadTwoAutomata(pre, pre, circuit);
            auto aut = autVec.at(0);
            autVec.erase(autVec.begin(), autVec.begin() + 2); // remove the first element
            bool verify = aut.execute(circuit, qp, autVec, params);
            if (!autVec.empty()) {
                if (verify) std::cout << "[OK] The circuit execution satisfies the loop invariant." << std::endl;
                else std::cout << "[ERROR] The circuit execution violates the loop invariant." << std::endl;
            }
            aut.print_language("OUTPUT:\n");
        }
    } else if (verification->parsed()) {
        // runConcrete = false;
        auto spec1 = ReadAutomaton(post);
        auto pre1 = ReadAutomaton(pre);
        if (std::holds_alternative<AUTOQ::SymbolicAutomata>(spec1) || std::holds_alternative<AUTOQ::SymbolicAutomata>(pre1) || AUTOQ::SymbolicAutomata::check_the_invariants_types(circuit) == "Symbolic") {
            // THROW_AUTOQ_ERROR("The postcondition must have concrete or predicate amplitudes.");
        // } else if (std::holds_alternative<AUTOQ::PredicateAutomata>(spec1)) {
            // auto &spec = std::get<AUTOQ::PredicateAutomata>(spec1);
            // spec.print_aut("POST:\n");
            // spec.print_language("POST:\n");
            auto aut1 = ReadAutomaton(pre);
            if (std::holds_alternative<AUTOQ::PredicateAutomata>(aut1)) {
                THROW_AUTOQ_ERROR("Predicate amplitudes cannot be used in a precondition.");
            }
            // auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadAutomaton(pre);
            auto [autVec, qp] = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic, AUTOQ::Symbol::Symbolic>::ReadTwoAutomata(pre, post, circuit);
            auto aut = autVec.at(0);
            auto spec = autVec.at(1);
            autVec.erase(autVec.begin(), autVec.begin() + 2); // remove the first two elements
            // aut.print_aut("PRE:\n");
            // aut.print_language("PRE:\n");
            bool verify = aut.execute(circuit, qp, autVec, params);
            // std::cout << "OUTPUT AUTOMATON:\n";
            // std::cout << "=================\n";
            // aut.print_aut("OUTPUT:\n");
            // aut.print_language("OUTPUT:\n");
            // std::cout << "=================\n";
            verify &= (aut <<= spec);
            // aut.print_language(); spec.print_language();
            if (latex) {
                aut.print_stats();
            } else {
                std::cout << "The quantum program has [" << aut.qubitNum << "] qubits and [" << AUTOQ::SymbolicAutomata::gateCount << "] gates. The verification process [" << (verify ? "OK" : "failed") << "] in [" << AUTOQ::Util::Convert::toString(chrono::steady_clock::now() - start) << "] with [" << AUTOQ::Util::getPeakRSS() / 1024 / 1024 << "MB] memory usage.\n";
            }
        } else if (std::holds_alternative<AUTOQ::PredicateAutomata>(spec1)) {
            THROW_AUTOQ_ERROR("PredicateAutomata as the postcondition are currently not supported.");
            // auto &spec = std::get<AUTOQ::PredicateAutomata>(spec1);
            // auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadAutomaton(pre); // TODO: can also be AUTOQ::Symbol::Concrete
            // // cannot use std::get<AUTOQ::SymbolicAutomata> here since ReadAutomaton(...) may treat "aut1" as a TreeAutomata
            // bool verify = aut.execute(circuit);
            // // std::cout << "OUTPUT AUTOMATON:\n";
            // // std::cout << "=================\n";
            // // aut.print_aut();
            // // std::cout << "=================\n";
            // verify &= (aut <<= spec);
            // // aut.print_language(); spec.print_language();
            // if (latex) {
            //     aut.print_stats();
            // } else {
            //     std::cout << "The quantum program has [" << aut.qubitNum << "] qubits and [" << AUTOQ::SymbolicAutomata::gateCount << "] gates. The verification process [" << (verify ? "OK" : "failed") << "] in [" << AUTOQ::Util::Convert::toString(chrono::steady_clock::now() - start) << "] with [" << AUTOQ::Util::getPeakRSS() / 1024 / 1024 << "MB] memory usage.\n";
            // }
        } else if (std::holds_alternative<AUTOQ::TreeAutomata>(spec1)) {
            // auto &spec = std::get<AUTOQ::TreeAutomata>(spec1);
            // // spec.print_aut("POST:\n");
            // // spec.print_language("POST:\n");
            auto aut1 = ReadAutomaton(pre);
            std::visit([](auto&& arg) {
                if constexpr (!std::is_same_v<std::decay_t<decltype(arg)>, AUTOQ::TreeAutomata>) {
                    THROW_AUTOQ_ERROR("When the postcondition has only concrete amplitudes, the precondition must also do so.");
                }
            }, aut1);
            auto [autVec, qp] = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadTwoAutomata(pre, post, circuit);
            auto aut = autVec.at(0);
            auto spec = autVec.at(1);
            autVec.erase(autVec.begin(), autVec.begin() + 2); // remove the first two elements
            // aut.print_language("PRE:\n");
            // spec.print_language("SPEC:\n");
            bool verify = aut.execute(circuit, qp, autVec, params);
            // std::cout << "OUTPUT AUTOMATON:\n";
            // std::cout << "=================\n";
            // aut.print_aut("OUTPUT:\n");
            // autMinus.value().print_aut("AUT-MINUS:\n");
            // aut.print_language("OUTPUT:\n");
            // std::cout << "=================\n";
            verify &= (aut <<= spec); // && (autMinus ? ((aut && (*autMinus)).empty()) : true);
            if (latex) {
                aut.print_stats();
            } else {
                std::cout << "The quantum program has [" << aut.qubitNum << "] qubits and [" << AUTOQ::TreeAutomata::gateCount << "] gates. The verification process [" << (verify ? "OK" : "failed") << "] in [" << AUTOQ::Util::Convert::toString(chrono::steady_clock::now() - start) << "] with [" << AUTOQ::Util::getPeakRSS() / 1024 / 1024 << "MB] memory usage.\n";
            }
        } else {
            THROW_AUTOQ_ERROR("Unsupported type of the postcondition.");
        }
    } else if (equivalence_checking->parsed()) {
        // runConcrete = true;
        /*AUTOQ::TreeAutomata*/ aut = AUTOQ::TreeAutomata::prefix_basis(extract_qubit(circuit1));
        /*AUTOQ::TreeAutomata*/ aut2 = AUTOQ::TreeAutomata::prefix_basis(extract_qubit(circuit2));
        aut.execute(circuit1, {}, {}, params);
        aut2.execute(circuit2, {}, {}, params);
        bool result = aut <<= aut2;
        if (latex) {
            // if (short_time) {
            //     std::map<std::string, std::string> stats;
            //     stats["gate"] = AUTOQ::Util::Convert::toString(AUTOQ::TreeAutomata::total_gate_time - AUTOQ::TreeAutomata::total_removeuseless_time - AUTOQ::TreeAutomata::total_reduce_time);
            //     stats["removeuseless"] = AUTOQ::Util::Convert::toString(AUTOQ::TreeAutomata::total_removeuseless_time);
            //     stats["reduce"] = AUTOQ::Util::Convert::toString(AUTOQ::TreeAutomata::total_reduce_time);
            //     stats["include"] = AUTOQ::Util::Convert::toString(AUTOQ::TreeAutomata::total_include_time);
            //     stats["total"] = AUTOQ::Util::Convert::toString(chrono::steady_clock::now() - start);
            //     stats["result"] = result ? "T" : "F";
            //     stats["aut1.trans"] = std::to_string(aut.count_transitions());
            //     stats["aut1.leaves"] = std::to_string(aut.count_leaves());
            //     stats["aut2.trans"] = std::to_string(aut2.count_transitions());
            //     stats["aut2.leaves"] = std::to_string(aut2.count_leaves());
            //     std::cout << AUTOQ::Util::Convert::ToString2(stats) << std::endl;
            // } else {
            //     std::cout << AUTOQ::Util::Convert::toString(chrono::steady_clock::now() - start) << " & " << (result ? "T" : "F") << "\n";
            // }
        } else {
            std::cout << "The two quantum programs are verified to be [" << (result ? "equal" : "unequal") << "] in [" << AUTOQ::Util::Convert::toString(chrono::steady_clock::now() - start) << "] with [" << AUTOQ::Util::getPeakRSS() / 1024 / 1024 << "MB] memory usage.\n";
        }
    } else if (print->parsed()) {
        auto aut = ReadAutomaton(pre);
        std::visit([](auto& aut){
            aut.print_language();
        }, aut);
    } else {
        THROW_AUTOQ_ERROR("Please provide at least one mode. Run \"autoq -h\" for more information.");
    }
    /**************/
    // if (long_time) {
    //     if (runConcrete)
    //         std::cout << "=\n"
    //                 << "The total time spent on gate operations (excluding remove_useless and reduce) is [" << AUTOQ::Util::Convert::toString(AUTOQ::TreeAutomata::total_gate_time - AUTOQ::TreeAutomata::total_removeuseless_time - AUTOQ::TreeAutomata::total_reduce_time) << "].\n"
    //                 << "The total time spent on remove_useless(...) is [" << AUTOQ::Util::Convert::toString(AUTOQ::TreeAutomata::total_removeuseless_time) << "].\n"
    //                 << "The total time spent on reduce(...) is [" << AUTOQ::Util::Convert::toString(AUTOQ::TreeAutomata::total_reduce_time) << "].\n"
    //                 << "The total time spent on check_inclusion(...) is [" << AUTOQ::Util::Convert::toString(AUTOQ::TreeAutomata::total_include_time) << "].\n";
    //     else
    //         std::cout << "=\n"
    //                 << "The total time spent on gate operations (excluding remove_useless and reduce) is [" << AUTOQ::Util::Convert::toString(AUTOQ::SymbolicAutomata::total_gate_time - AUTOQ::SymbolicAutomata::total_removeuseless_time - AUTOQ::SymbolicAutomata::total_reduce_time) << "].\n"
    //                 << "The total time spent on remove_useless(...) is [" << AUTOQ::Util::Convert::toString(AUTOQ::SymbolicAutomata::total_removeuseless_time) << "].\n"
    //                 << "The total time spent on reduce(...) is [" << AUTOQ::Util::Convert::toString(AUTOQ::SymbolicAutomata::total_reduce_time) << "].\n"
    //                 << "The total time spent on check_inclusion(...) is [" << AUTOQ::Util::Convert::toString(AUTOQ::SymbolicAutomata::total_include_time) << "].\n";
    // }
    /**************/
} catch (AutoQError &e) {
    std::cout << e.what() << std::endl;
}
    return 0;
}
