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
using AUTOQ::Util::ShellCmd;
using AUTOQ::Util::ReadFile;

int type, n;
std::string toString(std::chrono::steady_clock::duration tp);

int main(int argc, char **argv) {
    CLI::App app{" "}; //{"My CLI App"};

    bool latex = false; // Add a boolean flag option (no value)
    std::string pre, circuit, post;
    app.add_flag("-l,--latex", latex, "Print the statistics for tables in LaTeX");
    app.add_option("pre.{aut|hsl|spec}", pre, "the precondition file")->required()->type_name("");
    app.add_option("circuit.qasm", circuit, "the OpenQASM 3.0 circuit file")->required()->type_name("");
    app.add_option("post.{aut|hsl|spec}", post, "the postcondition file")->required()->type_name("");

    CLI11_PARSE(app, argc, argv); // Parse the command-line arguments

try {
    std::string constraint, constraintQ;
    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadAutomaton(pre);
    aut.remove_useless();
    aut.reduce();
    auto start = chrono::steady_clock::now();
    bool verify = aut.execute(circuit);
    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> Q = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadAutomaton(post);
    Q.remove_useless();
    Q.reduce();
    verify &= is_scaled_spec_satisfied(aut, Q);

    if (latex) {
        std::cout << aut.qubitNum << " & " << AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::gateCount
        << " & " << (verify ? "Passed" : "Failed") << " & " << toString(chrono::steady_clock::now() - start) << " & " << getPeakRSS() / 1024 / 1024 << "MB\n";
    } else {
        std::cout << "The quantum program has [" << aut.qubitNum << "] qubits and [" << AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::gateCount << "] gates.\nThe verification process [" << (verify ? "passed" : "failed") << "] with [" << toString(chrono::steady_clock::now() - start) << "] and [" << getPeakRSS() / 1024 / 1024 << "MB] memory usage.\n";
    }
    return 0;
} catch (std::exception &e) {
    std::cout << e.what() << std::endl;
    return 0;
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
