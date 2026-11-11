#ifndef AUTOQ_CLI_SPAN_COMMAND_HH
#define AUTOQ_CLI_SPAN_COMMAND_HH
#include <iostream>
#include <string>
#include <variant>
#include <CLI11.hpp>
#include "autoq/parsing/parser/timbuk_parser.hh"
#include "autoq/span/inclusion.hh"

struct SpanCommand {
    std::string a_path{}, b_path{};
    AUTOQ::Span::Options options{};
    CLI::App* command = nullptr;
    explicit SpanCommand(CLI::App& app) {
        command = app.add_subcommand("span-inclusion", "Check fixed-depth complex subspace inclusion (not language inclusion).");
        command->add_option("A", a_path, "Source automaton")->required();
        command->add_option("B", b_path, "Generator automaton")->required();
        command->add_option("--qubits", options.qubits, "Fixed depth n")->required();
        command->add_option("--max-runs", options.limits.runs, "Run limit applied separately to A and B; 0 disables")->check(CLI::NonNegativeNumber);
        command->add_option("--max-basis-runs", options.limits.basis, "Retained B basis limit; 0 disables")->check(CLI::NonNegativeNumber);
        command->add_option("--max-tuple-states", options.limits.tuples, "Cumulative tuple visits/frontier limit; 0 disables")->check(CLI::NonNegativeNumber);
        command->add_option("--max-equations", options.limits.equations, "Cumulative equation limit; 0 disables")->check(CLI::NonNegativeNumber);
        command->add_option("--max-search-steps", options.limits.search_steps, "Enumeration step limit, default 1000000; 0 disables")->check(CLI::NonNegativeNumber);
        command->add_option("--max-depth", options.limits.depth, "Depth guard, default 512; 0 disables")->check(CLI::NonNegativeNumber);
    }
    bool parsed() const { return command->parsed(); }
    int run() const {
        using namespace AUTOQ::Span;
        Result result;
        if (options.qubits < 0) {
            result.message = "Negative qubit depth";
        } else {
            const auto a = ReadAutomaton(a_path);
            const auto b = ReadAutomaton(b_path);
            if (!std::holds_alternative<AUTOQ::ConcreteAutomata>(a) ||
                !std::holds_alternative<AUTOQ::ConcreteAutomata>(b)) {
                result.message = "Only concrete automata are supported";
            } else {
                result = check_inclusion(std::get<AUTOQ::ConcreteAutomata>(a),
                                         std::get<AUTOQ::ConcreteAutomata>(b), options);
            }
        }
        std::cout << "Span inclusion outcome: " << to_string(result.outcome)
                  << " (B runs: " << result.stats.b_runs
                  << ", retained basis: " << result.stats.basis
                  << ", A runs: " << result.stats.a_runs
                  << ", tuple visits: " << result.stats.tuples
                  << ", equations: " << result.stats.equations
                  << ", search steps: " << result.stats.search_steps << ")";
        if (!result.message.empty()) std::cout << " - " << result.message;
        std::cout << '\n';
        switch (result.outcome) {
            case Outcome::Included: return 0;
            case Outcome::NotIncluded: return 2;
            case Outcome::ResourceLimit: return 3;
            case Outcome::UnsupportedInput: return 4;
        }
        return 4;
    }
};
#endif
