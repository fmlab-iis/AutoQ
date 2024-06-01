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

#include <CLI11.hpp>

using namespace std;

std::string toString(std::chrono::steady_clock::duration tp);

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

int main(int argc, char **argv) {
    CLI::App app{" "}; //{"My CLI App"};
    std::string pre, circuit, post, constraint, circuit1, circuit2;

    CLI::App* executionC = app.add_subcommand("exC", "executionC");
    executionC->add_option("pre.{aut|hsl|spec}", pre, "the precondition file")->required()->type_name("");
    executionC->add_option("circuit.qasm", circuit, "the OpenQASM 3.0 circuit file")->required()->type_name("");

    bool latex = false;
    CLI::App* verificationC = app.add_subcommand("verC", "verificationC");
    verificationC->add_option("pre.{aut|hsl|spec}", pre, "the precondition file")->required()->type_name("");
    verificationC->add_option("circuit.qasm", circuit, "the OpenQASM 3.0 circuit file")->required()->type_name("");
    verificationC->add_option("post.{aut|hsl|spec}", post, "the postcondition file")->required()->type_name("");
    verificationC->add_flag("-l,--latex", latex, "Print the statistics for tables in LaTeX");

    CLI::App* executionS = app.add_subcommand("exS", "executionS");
    executionS->add_option("pre.{aut|hsl|spec}", pre, "the precondition file")->required()->type_name("");
    executionS->add_option("circuit.qasm", circuit, "the OpenQASM 3.0 circuit file")->required()->type_name("");

    CLI::App* verificationS = app.add_subcommand("verS", "verificationS");
    verificationS->add_option("pre.{aut|hsl|spec}", pre, "the precondition file")->required()->type_name("");
    verificationS->add_option("circuit.qasm", circuit, "the OpenQASM 3.0 circuit file")->required()->type_name("");
    verificationS->add_option("post.{aut|hsl|spec}", post, "the postcondition file")->required()->type_name("");
    verificationS->add_option("constraint.smt", constraint, "the constraint file")->type_name("");

    CLI::App* equivalence_checking = app.add_subcommand("eq", "equivalence checking");
    equivalence_checking->add_option("circuit1.qasm", circuit1, "the OpenQASM 2.0 circuit file")->required()->type_name("");
    equivalence_checking->add_option("circuit2.qasm", circuit2, "the OpenQASM 2.0 circuit file")->required()->type_name("");
    equivalence_checking->add_flag("-l,--latex", latex, "Print the statistics for tables in LaTeX");

    bool short_time = false, long_time = false;
    app.add_flag("-t", short_time, "print times");
    app.add_flag("--time", long_time, "print times");
    CLI11_PARSE(app, argc, argv); // Parse the command-line arguments

    auto start = chrono::steady_clock::now();
    bool runConcrete; // or runSymbolic
    if (executionC->parsed()) {
        runConcrete = true;
        AUTOQ::TreeAutomata aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::FromFileToAutomata(pre);
        aut.execute(circuit);
        aut.print_aut();
    } else if (verificationC->parsed()) {
        runConcrete = true;
        auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::FromFileToAutomata(pre);
        auto aut2 = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::FromFileToAutomata(post);
        aut.execute(circuit);
        bool verify = AUTOQ::TreeAutomata::check_inclusion(aut, aut2);
        if (latex) {
            aut.print_stats();
        } else {
            std::cout << "The quantum program has [" << aut.qubitNum << "] qubits and [" << AUTOQ::TreeAutomata::gateCount << "] gates.\nThe verification process [" << (verify ? "passed" : "failed") << "] in [" << toString(chrono::steady_clock::now() - start) << "] with [" << getPeakRSS() / 1024 / 1024 << "MB] memory usage.\n";
        }
    } else if (executionS->parsed()) {
        runConcrete = false;
        AUTOQ::SymbolicAutomata aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::FromFileToAutomata(pre);
        aut.execute(circuit);
        aut.print_aut();
    } else if (verificationS->parsed()) {
        runConcrete = false;
        AUTOQ::SymbolicAutomata aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::FromFileToAutomata(pre);
        AUTOQ::PredicateAutomata spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>::FromFileToAutomata(post);

        std::stringstream buffer;
        if (!constraint.empty()) {
            std::ifstream t(constraint);
            if (!t) // in case the file could not be open
                throw std::runtime_error("[ERROR] Failed to open file " + std::string(constraint) + ".");
            buffer << t.rdbuf();
        }
        AUTOQ::Constraint C(buffer.str().c_str());

        aut.execute(circuit);
        // std::cout << "OUTPUT AUTOMATON:\n";
        // std::cout << "=================\n";
        // aut.print_aut();
        // std::cout << "=================\n";
        bool verify = AUTOQ::check_inclusion(C, aut, spec);
        if (latex) {
            aut.print_stats();
        } else {
            std::cout << "The quantum program has [" << aut.qubitNum << "] qubits and [" << AUTOQ::SymbolicAutomata::gateCount << "] gates.\nThe verification process [" << (verify ? "passed" : "failed") << "] in [" << toString(chrono::steady_clock::now() - start) << "] with [" << getPeakRSS() / 1024 / 1024 << "MB] memory usage.\n";
        }
    } else if (equivalence_checking->parsed()) {
        runConcrete = true;
        AUTOQ::TreeAutomata aut = AUTOQ::TreeAutomata::prefix_basis(extract_qubit(circuit1));
        AUTOQ::TreeAutomata aut2 = AUTOQ::TreeAutomata::prefix_basis(extract_qubit(circuit2));
        aut.execute(circuit1);
        aut2.execute(circuit2);
        bool result = AUTOQ::TreeAutomata::check_inclusion(aut, aut2);
        if (latex) {
            if (short_time) {
                std::cout << toString(AUTOQ::TreeAutomata::total_gate_time - AUTOQ::TreeAutomata::total_removeuseless_time - AUTOQ::TreeAutomata::total_reduce_time) << ","
                          << toString(AUTOQ::TreeAutomata::total_removeuseless_time) << ","
                          << toString(AUTOQ::TreeAutomata::total_reduce_time) << ","
                          << toString(AUTOQ::TreeAutomata::total_include_time) << " & " << (result ? "T" : "F") << "\n";
            } else {
                std::cout << toString(chrono::steady_clock::now() - start) << " & " << (result ? "T" : "F") << "\n";
            }
        } else {
            std::cout << "The two quantum programs are verified to be [" << (result ? "equal" : "unequal") << "] in [" << toString(chrono::steady_clock::now() - start) << "] with [" << getPeakRSS() / 1024 / 1024 << "MB] memory usage.\n";
        }
    }
    /**************/
    if (long_time) {
        if (runConcrete)
            std::cout << "=\n"
                    << "The total time spent on gate operations (excluding remove_useless and reduce) is [" << toString(AUTOQ::TreeAutomata::total_gate_time - AUTOQ::TreeAutomata::total_removeuseless_time - AUTOQ::TreeAutomata::total_reduce_time) << "].\n"
                    << "The total time spent on remove_useless(...) is [" << toString(AUTOQ::TreeAutomata::total_removeuseless_time) << "].\n"
                    << "The total time spent on reduce(...) is [" << toString(AUTOQ::TreeAutomata::total_reduce_time) << "].\n"
                    << "The total time spent on check_inclusion(...) is [" << toString(AUTOQ::TreeAutomata::total_include_time) << "].\n";
        else
            std::cout << "=\n"
                    << "The total time spent on gate operations (excluding remove_useless and reduce) is [" << toString(AUTOQ::SymbolicAutomata::total_gate_time - AUTOQ::SymbolicAutomata::total_removeuseless_time - AUTOQ::SymbolicAutomata::total_reduce_time) << "].\n"
                    << "The total time spent on remove_useless(...) is [" << toString(AUTOQ::SymbolicAutomata::total_removeuseless_time) << "].\n"
                    << "The total time spent on reduce(...) is [" << toString(AUTOQ::SymbolicAutomata::total_reduce_time) << "].\n"
                    << "The total time spent on check_inclusion(...) is [" << toString(AUTOQ::SymbolicAutomata::total_include_time) << "].\n";
    }
    /**************/
    return 0;
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
