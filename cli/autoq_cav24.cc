#include <iostream>
#include <chrono>

#include "autoq/parsing/timbuk_parser.hh"
#include "autoq/aut_description.hh"
#include "autoq/util/util.hh"
#include "CLI11.hpp"

int main(int argc, char **argv) {
    CLI::App app{" "}; //{"My CLI App"};

    bool latex = false; // Add a boolean flag option (no value)
    std::string pre, circuit, post;
    app.add_flag("-l,--latex", latex, "Print the statistics for tables in LaTeX");
    app.add_option("pre.{hsl|spec}", pre, "the precondition file")->required()->type_name("");
    app.add_option("circuit.qasm", circuit, "the OpenQASM 3.0 circuit file")->required()->type_name("");
    app.add_option("post.{hsl|spec}", post, "the postcondition file")->required()->type_name("");

    CLI11_PARSE(app, argc, argv); // Parse the command-line arguments

    bool useSymbolic = false;
    AUTOQ::Automata<AUTOQ::Symbol::Concrete> aut;
    AUTOQ::Automata<AUTOQ::Symbol::Concrete> Q;
try {
    aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(pre);
    Q = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(post);
    AUTOQ::Automata<AUTOQ::Symbol::Concrete>::check_the_invariants_types(circuit);
    // The above section tries to check if the concrete algorithm can be used.
} catch (std::exception &e) {
    useSymbolic = true;
}

try {
    if (!useSymbolic) {
        aut.remove_useless();
        aut.reduce();
        auto start = std::chrono::steady_clock::now();
        bool verify = aut.execute(circuit);
        Q.remove_useless();
        Q.reduce();
        verify &= (aut <<= Q);
        if (latex) {
            std::cout << aut.qubitNum << " & " << AUTOQ::Automata<AUTOQ::Symbol::Concrete>::gateCount
            << " & " << (verify ? "Passed" : "Failed") << " & " << AUTOQ::Util::print_duration(std::chrono::steady_clock::now() - start) << " & " << AUTOQ::Util::getPeakRSS() / 1024 / 1024 << "MB\n";
        } else {
            std::cout << "The quantum program has [" << aut.qubitNum << "] qubits and [" << AUTOQ::Automata<AUTOQ::Symbol::Concrete>::gateCount << "] gates.\nThe verification process [" << (verify ? "passed" : "failed") << "] with a running time of [" << AUTOQ::Util::print_duration(std::chrono::steady_clock::now() - start) << "] and a memory usage of [" << AUTOQ::Util::getPeakRSS() / 1024 / 1024 << "MB].\n";
        }
    } else {
        AUTOQ::Automata<AUTOQ::Symbol::Symbolic> aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadAutomaton(pre);
        aut.remove_useless();
        aut.reduce();
        auto start = std::chrono::steady_clock::now();
        bool verify = aut.execute(circuit);
        AUTOQ::Automata<AUTOQ::Symbol::Symbolic> Q = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadAutomaton(post);
        Q.remove_useless();
        Q.reduce();
        verify &= (aut <<= Q);
        // aut.print_language(); Q.print_language();
        if (latex) {
            std::cout << aut.qubitNum << " & " << AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::gateCount
            << " & " << (verify ? "Passed" : "Failed") << " & " << AUTOQ::Util::print_duration(std::chrono::steady_clock::now() - start) << " & " << AUTOQ::Util::getPeakRSS() / 1024 / 1024 << "MB\n";
        } else {
            std::cout << "The quantum program has [" << aut.qubitNum << "] qubits and [" << AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::gateCount << "] gates.\nThe verification process [" << (verify ? "passed" : "failed") << "] with a running time of [" << AUTOQ::Util::print_duration(std::chrono::steady_clock::now() - start) << "] and a memory usage of [" << AUTOQ::Util::getPeakRSS() / 1024 / 1024 << "MB].\n";
        }
    }
} catch (std::exception &e) {
    std::cout << e.what() << std::endl;
}
    return 0;
}
