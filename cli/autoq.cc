#include <fstream>
#include <sstream>
#include <iostream>
#include "autoq/error.hh"
#include "autoq/error_messages.hh"
#include "autoq/parsing/parser/timbuk_parser.hh"
#include "autoq/serialization/timbuk_serializer.hh"
#include "autoq/aut_description.hh"
#include "autoq/inclusion.hh"
#include "autoq/span/inclusion.hh"
#include "autoq/util/types.hh"
#include "autoq/util/util.hh"
#include "autoq/util/string.hh"
#include "autoq/parsing/ExtendedDirac/EvaluationVisitor.h"
#include "autoq/util/qasm_n_tuple.hh"
#include "autoq/complex/complex.hh"
#include <sys/wait.h>
#include <unistd.h>
#include <chrono>
#include <iomanip>
#include <regex>
#include <fenv.h>
#ifdef __APPLE__
#include <fenv_darwin.h>
#endif
#include <CLI11.hpp>
#include <version.h>

using namespace std;

constexpr int kExtractQubitError = -1;

int extract_qubit(const std::string& filename) {
    std::ifstream file(filename);
    if (!file.is_open()) {
        AUTOQ::Util::Log::error("Unable to open file");
        return kExtractQubitError;
    }

    std::string line;
    std::regex pattern(R"(qreg\s+\w+\[(\d+)\];)");
    std::smatch match;
    while (std::getline(file, line)) {
        if (std::regex_search(line, match, pattern)) {
            return std::stoi(match[1].str());
        }
    }

    AUTOQ::Util::Log::error("Pattern not found");
    return kExtractQubitError;
}

namespace {
constexpr size_t kBytesPerMB = 1024 * 1024;

// CLI option names (placeholder names in help)
const char* kOptPreHsl = "pre.hsl";
const char* kOptCircuitQasm = "circuit.qasm";
const char* kOptPostHsl = "post.hsl";
const char* kOptCircuit1Qasm = "circuit1.qasm";
const char* kOptCircuit2Qasm = "circuit2.qasm";
const char* kOptStatesHsl = "states.hsl";

// CLI option description strings (reused across subcommands)
const char* kPreFileOpt = "the precondition file";
const char* kPostFileOpt = "the postcondition file";
const char* kStatesFileOpt = "the automaton file";
const char* kCircuitFileOpt = "the OpenQASM 2.0 or 3.0 circuit file";
const char* kLoopsumOpt = "Summarize loops using symbolic execution.";
const char* kLatexOpt = "Print the statistics for tables in LaTeX.";

// Parameter key and values for loop execution mode
const char* kParamLoop = "loop";
const char* kLoopManual = "manual";
const char* kLoopSymbolic = "symbolic";

// Number of elements to remove from autVec after ReadTwoAutomata (pre+circuit or aut+spec)
constexpr size_t kAutVecEraseCount = 2;

namespace EM = AUTOQ::ErrorMessages;

const char* kOutputLabel = "OUTPUT:\n";

void print_verification_result(int qubitNum, int gateCount, bool verify,
                               const chrono::steady_clock::time_point& start) {
    std::ostringstream oss;
    oss << "The quantum program has [" << qubitNum << "] qubits and ["
        << gateCount << "] gates. The verification process ["
        << (verify ? "OK" : "failed") << "] in ["
        << AUTOQ::Util::Convert::ToString(chrono::steady_clock::now() - start)
        << "] with [" << (AUTOQ::Util::getPeakRSS() / kBytesPerMB) << "MB] memory usage.";
    AUTOQ::Util::Log::info(oss.str());
}

void print_loop_invariant_result(bool verify) {
    AUTOQ::Util::Log::info(verify ? "[OK] The circuit execution satisfies the loop invariant."
                                  : "[ERROR] The circuit execution violates the loop invariant.");
}

void print_equivalence_result(bool result,
                               const chrono::steady_clock::time_point& start) {
    std::ostringstream oss;
    oss << "The two quantum programs are verified to be ["
        << (result ? "equal" : "unequal") << "] in ["
        << AUTOQ::Util::Convert::ToString(chrono::steady_clock::now() - start)
        << "] with [" << (AUTOQ::Util::getPeakRSS() / kBytesPerMB) << "MB] memory usage.";
    AUTOQ::Util::Log::info(oss.str());
}
}  // namespace

using AUTOQ::adjust_N_in_nTuple;

template<typename Symbol>
static void run_execution_impl(const std::string& pre, const std::string& circuit,
                               const ParameterMap& params) {
    auto [autVec, qp] = AUTOQ::Parsing::TimbukParser<Symbol>::ReadTwoAutomata(pre, pre, circuit);
    auto aut = autVec.at(0);
    autVec.erase(autVec.begin(), autVec.begin() + kAutVecEraseCount);
    bool verify = aut.execute(circuit, qp, autVec, params);
    if (!autVec.empty()) print_loop_invariant_result(verify);
    aut.print_language(kOutputLabel);
}

static void run_execution(const std::string& pre, const std::string& circuit,
                          const ParameterMap& params) {
    auto aut1 = ReadAutomaton(pre);
    if (std::holds_alternative<AUTOQ::PredicateAutomata>(aut1)) {
        THROW_AUTOQ_ERROR(EM::kPredicatePrecondition);
    }
    if (std::holds_alternative<AUTOQ::SymbolicAutomata>(aut1) || AUTOQ::SymbolicAutomata::check_the_invariants_types(circuit) == "Symbolic")
        run_execution_impl<AUTOQ::Symbol::Symbolic>(pre, circuit, params);
    else
        run_execution_impl<AUTOQ::Symbol::Concrete>(pre, circuit, params);
}

static void run_equivalence(const std::string& circuit1, const std::string& circuit2,
                           const ParameterMap& params, bool latex,
                           const chrono::steady_clock::time_point& start) {
    int n1 = extract_qubit(circuit1);
    if (n1 == kExtractQubitError)
        THROW_AUTOQ_ERROR("Cannot extract qubit count from circuit: " + circuit1);
    int n2 = extract_qubit(circuit2);
    if (n2 == kExtractQubitError)
        THROW_AUTOQ_ERROR("Cannot extract qubit count from circuit: " + circuit2);
    AUTOQ::ConcreteAutomata aut = AUTOQ::ConcreteAutomata::prefix_basis(n1);
    AUTOQ::ConcreteAutomata aut2 = AUTOQ::ConcreteAutomata::prefix_basis(n2);
    aut.execute(circuit1, {}, {}, params);
    aut2.execute(circuit2, {}, {}, params);
    bool result = aut <<= aut2;
    if (latex) {
        // (latex stats output commented out)
    } else {
        print_equivalence_result(result, start);
    }
}

template<typename Symbol>
static void run_verification_impl(const std::string& pre, const std::string& post, const std::string& circuit,
                                  const ParameterMap& params, bool latex,
                                  const chrono::steady_clock::time_point& start) {
    auto& st = AUTOQ::default_execution_stats();
    st.startFromFileToAutomata = std::chrono::steady_clock::now();
    auto [autVec, qp] = AUTOQ::Parsing::TimbukParser<Symbol>::ReadTwoAutomata(pre, post, circuit);
    st.endFromFileToAutomata = std::chrono::steady_clock::now();
    auto aut = autVec.at(0);
    auto spec = autVec.at(1);
    autVec.erase(autVec.begin(), autVec.begin() + kAutVecEraseCount);
    bool verify = aut.execute(circuit, qp, autVec, params);
    verify &= (aut <<= spec);
    if (latex)
        aut.print_stats();
    else
        print_verification_result(aut.qubitNum, aut.execution_stats()->gateCount, verify, start);
}

static void run_verification(const std::string& pre, const std::string& post, const std::string& circuit,
                             const ParameterMap& params, bool latex,
                             const chrono::steady_clock::time_point& start) {
    auto spec1 = ReadAutomaton(post);
    auto pre1 = ReadAutomaton(pre);
    if (std::holds_alternative<AUTOQ::SymbolicAutomata>(spec1) || std::holds_alternative<AUTOQ::SymbolicAutomata>(pre1) || AUTOQ::SymbolicAutomata::check_the_invariants_types(circuit) == "Symbolic") {
        if (std::holds_alternative<AUTOQ::PredicateAutomata>(pre1))
            THROW_AUTOQ_ERROR(EM::kPredicatePrecondition);
        run_verification_impl<AUTOQ::Symbol::Symbolic>(pre, post, circuit, params, latex, start);
    } else if (std::holds_alternative<AUTOQ::PredicateAutomata>(spec1)) {
        THROW_AUTOQ_ERROR(EM::kPredicateAutomataPost);
    } else if (std::holds_alternative<AUTOQ::ConcreteAutomata>(spec1)) {
        std::visit([](auto&& arg) {
            if constexpr (!std::is_same_v<std::decay_t<decltype(arg)>, AUTOQ::ConcreteAutomata>)
                THROW_AUTOQ_ERROR(EM::kConcretePostPre);
        }, pre1);
        run_verification_impl<AUTOQ::Symbol::Concrete>(pre, post, circuit, params, latex, start);
    } else {
        THROW_AUTOQ_ERROR(EM::kUnsupportedPostType);
    }
}

static AUTOQ::Span::Result run_span_inclusion(
    const std::string &a_path,
    const std::string &b_path,
    int qubits,
    const AUTOQ::Span::ResourceLimits &limits)
{
    AUTOQ::Span::Options opts;
    opts.qubits = qubits;
    opts.limits = limits;
    return AUTOQ::Span::check_inclusion(ReadAutomaton(a_path), ReadAutomaton(b_path), opts);
}

int main(int argc, char **argv) {
try {
    // set_timeout(600);
#ifndef __EMSCRIPTEN__  // WebAssembly has no floating-point exception traps
    feenableexcept(FE_ALL_EXCEPT & ~FE_INEXACT);
#endif

    CLI::App app{"AutoQ 2.0: An automata-based C++ tool for quantum program verification."};
    std::string pre, circuit, post, circuit1, circuit2;

    bool summarize_loops = false;
    std::string span_a, span_b;
    int span_qubits = -1;
    std::size_t span_max_basis_runs = 0;
    std::size_t span_max_b_runs = 0;
    std::size_t span_max_a_runs = 0;
    std::size_t span_max_tuple_states = 0;
    std::size_t span_max_equations = 0;
    CLI::App* execution = app.add_subcommand("ex", "Execute a quantum circuit with a given precondition.");
    execution->add_option(kOptPreHsl, pre, kPreFileOpt)->required()->type_name("");
    execution->add_option(kOptCircuitQasm, circuit, kCircuitFileOpt)->required()->type_name("");
    execution->add_flag("--loopsum", summarize_loops, kLoopsumOpt);
    execution->callback([&]() {
        adjust_N_in_nTuple(circuit);
    });

    bool latex = false;
    CLI::App* verification = app.add_subcommand("ver", "Verify the execution result against a given postcondition.");
    verification->add_option(kOptPreHsl, pre, kPreFileOpt)->required()->type_name("");
    verification->add_option(kOptCircuitQasm, circuit, kCircuitFileOpt)->required()->type_name("");
    verification->add_option(kOptPostHsl, post, kPostFileOpt)->required()->type_name("");
    verification->add_flag("--loopsum", summarize_loops, kLoopsumOpt);
    verification->add_flag("-l,--latex", latex, kLatexOpt);
    verification->callback([&]() {
        adjust_N_in_nTuple(circuit);
    });

    CLI::App* equivalence_checking = app.add_subcommand("eq", "Check equivalence of two given quantum circuits.");
    equivalence_checking->add_option(kOptCircuit1Qasm, circuit1, kCircuitFileOpt)->required()->type_name("");
    equivalence_checking->add_option(kOptCircuit2Qasm, circuit2, kCircuitFileOpt)->required()->type_name("");
    equivalence_checking->add_flag("--loopsum", summarize_loops, kLoopsumOpt);
    equivalence_checking->add_flag("-l,--latex", latex, kLatexOpt);
    equivalence_checking->callback([&]() {
        adjust_N_in_nTuple(circuit1);
        adjust_N_in_nTuple(circuit2);
    });

    CLI::App* print = app.add_subcommand("print", "Print the set of quantum states.");
    print->add_option(kOptStatesHsl, pre, kStatesFileOpt)->required()->type_name("");

    CLI::App* span_inclusion = app.add_subcommand("span-inclusion", "Check whether span_C(L_n(A)) is included in span_C(L_n(B)) at fixed qubit depth.");
    span_inclusion->add_option("A.lsta", span_a, "source concrete automaton A")->required()->type_name("");
    span_inclusion->add_option("B.lsta", span_b, "source concrete automaton B")->required()->type_name("");
    span_inclusion->add_option("--qubits", span_qubits, "fixed qubit depth n")->required();
    span_inclusion->add_option("--max-basis-runs", span_max_basis_runs, "resource limit for retained basis runs in B (0 = unlimited)");
    span_inclusion->add_option("--max-b-runs", span_max_b_runs, "resource limit for enumerated B runs (0 = unlimited)");
    span_inclusion->add_option("--max-a-runs", span_max_a_runs, "resource limit for enumerated A runs (0 = unlimited)");
    span_inclusion->add_option("--max-tuple-states", span_max_tuple_states, "resource limit for tuple-state traversal (0 = unlimited)");
    span_inclusion->add_option("--max-equations", span_max_equations, "resource limit for solver equations (0 = unlimited)");

    CLI::Option* version = app.add_flag("-v,--version", "Print the full Git commit hash ID.");

    // bool short_time = false, long_time = false;
    // app.add_flag("-t", short_time, "print times");
    // app.add_flag("--time", long_time, "print times");
    CLI11_PARSE(app, argc, argv); // Parse the command-line arguments

    if (*version) {
        AUTOQ::Util::Log::info(AUTOQ_GIT_SHA);
        return 0;
    }

    auto start = chrono::steady_clock::now();
    int exit_code = 0;
    // bool runConcrete; // or runSymbolic
    ParameterMap params;
    params[kParamLoop] = kLoopManual;
    if (summarize_loops) {
        params[kParamLoop] = kLoopSymbolic;
    }
    if (execution->parsed()) {
        run_execution(pre, circuit, params);
    } else if (verification->parsed()) {
        run_verification(pre, post, circuit, params, latex, start);
    } else if (equivalence_checking->parsed()) {
        run_equivalence(circuit1, circuit2, params, latex, start);
    } else if (print->parsed()) {
        auto aut = ReadAutomaton(pre);
        std::visit([](auto& aut){
            aut.print_language();
        }, aut);
    } else if (span_inclusion->parsed()) {
        AUTOQ::Span::ResourceLimits limits;
        limits.max_basis_runs = span_max_basis_runs;
        limits.max_b_runs = span_max_b_runs;
        limits.max_a_runs = span_max_a_runs;
        limits.max_tuple_states = span_max_tuple_states;
        limits.max_equations = span_max_equations;

        const auto result = run_span_inclusion(span_a, span_b, span_qubits, limits);
        std::ostringstream oss;
        oss << "Span inclusion outcome: " << AUTOQ::Span::to_string(result.outcome)
            << " (B runs: " << result.stats.b_runs_enumerated
            << ", retained basis: " << result.stats.basis_runs_retained
            << ", A runs: " << result.stats.a_runs_enumerated
            << ", tuple states: " << result.stats.tuple_states_visited
            << ", equations: " << result.stats.equations_added << ")";
        if (!result.message.empty()) {
            oss << " - " << result.message;
        }
        AUTOQ::Util::Log::info(oss.str());

        switch (result.outcome) {
            case AUTOQ::Span::Outcome::Included:
                exit_code = 0;
                break;
            case AUTOQ::Span::Outcome::NotIncluded:
                exit_code = 2;
                break;
            case AUTOQ::Span::Outcome::ResourceLimit:
                exit_code = 3;
                break;
            case AUTOQ::Span::Outcome::UnsupportedInput:
                exit_code = 4;
                break;
        }
    } else {
        THROW_AUTOQ_ERROR(EM::kNoMode);
    }
    /**************/
    // if (long_time) {
    //     if (runConcrete)
    //         std::cout << "=\n"
    //                 << "The total time spent on gate operations (excluding remove_useless and reduce) is [" << AUTOQ::Util::Convert::ToString(AUTOQ::ConcreteAutomata::total_gate_time - AUTOQ::ConcreteAutomata::total_removeuseless_time - AUTOQ::ConcreteAutomata::total_reduce_time) << "].\n"
    //                 << "The total time spent on remove_useless(...) is [" << AUTOQ::Util::Convert::ToString(AUTOQ::ConcreteAutomata::total_removeuseless_time) << "].\n"
    //                 << "The total time spent on reduce(...) is [" << AUTOQ::Util::Convert::ToString(AUTOQ::ConcreteAutomata::total_reduce_time) << "].\n"
    //                 << "The total time spent on check_inclusion(...) is [" << AUTOQ::Util::Convert::ToString(AUTOQ::ConcreteAutomata::total_include_time) << "].\n";
    //     else
    //         std::cout << "=\n"
    //                 << "The total time spent on gate operations (excluding remove_useless and reduce) is [" << AUTOQ::Util::Convert::ToString(AUTOQ::SymbolicAutomata::total_gate_time - AUTOQ::SymbolicAutomata::total_removeuseless_time - AUTOQ::SymbolicAutomata::total_reduce_time) << "].\n"
    //                 << "The total time spent on remove_useless(...) is [" << AUTOQ::Util::Convert::ToString(AUTOQ::SymbolicAutomata::total_removeuseless_time) << "].\n"
    //                 << "The total time spent on reduce(...) is [" << AUTOQ::Util::Convert::ToString(AUTOQ::SymbolicAutomata::total_reduce_time) << "].\n"
    //                 << "The total time spent on check_inclusion(...) is [" << AUTOQ::Util::Convert::ToString(AUTOQ::SymbolicAutomata::total_include_time) << "].\n";
    // }
    /**************/
} catch (AutoQError &e) {
    AUTOQ::Util::Log::error(e.what());
    return 1;
}
    return exit_code;
}
