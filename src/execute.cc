/**
 * QASM execution: parse and run circuits, loops, gates.
 * - execute(filename), parse_for_loop_body, parse_qubit_indices.
 * - handle_while_loop_start, handle_if_block_start, handle_else, handle_closing_brace.
 * - single_gate_execute, check_the_invariants_types.
 */
#include "autoq/error_messages.hh"
#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/symbol/predicate.hh"
#include "autoq/util/string.hh"
#include "autoq/loop_summarization.hh"
#include "autoq/aut_description.hh"
#include "autoq/parsing/parser/timbuk_parser.hh"
#include "autoq/parsing/complex_parser.hh"
#include "autoq/parsing/ExtendedDirac/EvaluationVisitor.h"
#include "autoq/parsing/angle.hh"
#include <regex>
#include <fstream>
#include <filesystem>
#include <functional>
#include <numeric>

namespace {

const std::sregex_iterator kRegexEnd;

/** Reads lines from \a qasm until a line starting with "}". Sets \a in_loop to false on success.
 *  (\a is Doxygen syntax: it marks the following word as a parameter name.) */
std::vector<std::string> parse_for_loop_body(std::ifstream& qasm, bool& in_loop) {
    std::vector<std::string> loop_body;
    std::string line;
    while (std::getline(qasm, line)) {
        line = AUTOQ::String::trim(line);
        if (line.find("{") == 0)
            continue;
        if (line.find("}") == 0) {
            in_loop = false;
            return loop_body;
        }
        loop_body.push_back(line);
    }
    THROW_AUTOQ_ERROR(AUTOQ::ErrorMessages::kLoopNotEnded);
}

int first_qubit_index(const std::string& line, const AUTOQ::QasmRegexes& re,
                      const std::vector<int>& qubit_permutation) {
    std::smatch m;
    return std::regex_search(line, m, re.digit)
           ? (1 + qubit_permutation[atoi(m[0].str().c_str())])
           : -1;
}

std::vector<int> parse_qubit_indices(const std::string& line, const AUTOQ::QasmRegexes& re,
                     const std::vector<int>& qubit_permutation) {
    std::vector<int> pos;
    std::sregex_iterator it(line.begin(), line.end(), re.digit);
    while (it != kRegexEnd) {
        pos.push_back(1 + qubit_permutation[atoi(it->str().c_str())]);
        ++it;
    }
    return pos;
}

}  // namespace

namespace EM = AUTOQ::ErrorMessages;

template <typename Symbol>
bool AUTOQ::Automata<Symbol>::execute(const std::string &filename, std::vector<int> qubit_permutation, const std::vector<AUTOQ::Automata<Symbol>> &loopInvariants, ParameterMap params) {
    return execute(filename.c_str(), qubit_permutation, loopInvariants, params);
}
template <typename Symbol>
bool AUTOQ::Automata<Symbol>::execute(const char *filename, std::vector<int> qubit_permutation, const std::vector<AUTOQ::Automata<Symbol>> &loopInvariants, ParameterMap params) {
    if (params.find("loop") == params.end()) params["loop"] = "manual";
    initialize_stats();
    if (qubit_permutation.empty()) {
        qubit_permutation.resize(qubitNum);
        std::iota(qubit_permutation.begin(), qubit_permutation.end(), 0); // fills with 0..n-1
    }

    int loopInvariantCounter = 0;
    bool verify = true;
    bool inGateDef = false;
    bool inWhileLoop = false;
    bool inIfBlock = false;
    bool inElseBlock = false;
    std::map<std::string, int> var_is_measure_what_qubit;
    std::string while_measurement_guard;
    AUTOQ::Automata<Symbol> I, measure_to_continue, measure_to_break, measure_to_else, result_after_if;
    std::ifstream qasm(filename);
    const AUTOQ::QasmRegexes qasm_re{};

    if (!qasm.is_open()) THROW_AUTOQ_ERROR(std::string(EM::kOpenFilePrefix) + filename + ".");
    std::string line, previous_line;

    bool in_loop = false; // nested loops are not yet taken into consideration
    while (getline(qasm, line)) {
        line = AUTOQ::String::trim(line);
        if (line.empty()) continue;
        // AUTOQ_DEBUG("[" << (lineno++) << "]: " << line);
        if (inGateDef) {
            if (line.find("}") != std::string::npos) {
                inGateDef = false;
            }
            continue; // simply ignore gate definitions
        }
        if (line.find("OPENQASM") == 0 || line.find("include ") == 0 || line.find("//") == 0 || line.find("/*") == 0 || line.find("bit") == 0) continue;
        if (line.find("qreg ") == 0 || line.find("qubit") == 0) {
            std::sregex_iterator it(line.begin(), line.end(), qasm_re.digit);
            while (it != kRegexEnd) {
                if (atoi(it->str().c_str()) != static_cast<int>(qubitNum))
                    THROW_AUTOQ_ERROR(EM::kQubitMismatch);
                ++it;
            }
        } else if (line.find("for ") == 0) {
            if (in_loop) THROW_AUTOQ_ERROR(EM::kNestedLoops);
            in_loop = true;
            std::smatch match_pieces;
            std::regex_search(line, match_pieces, qasm_re.loop);
            std::vector<std::string> loop_body = parse_for_loop_body(qasm, in_loop);
            execute_loop<Symbol>(loop_body, *this, params, qasm_re, match_pieces, qubit_permutation);
        } else if (line.find("PRINT_STATS") == 0) {
            print_stats(previous_line, true);
        } else if (line.find("PRINT_AUT") == 0) {
            print_aut();
        } else if (line.find("PRINT_LANG") == 0) {
            print_language();
        } else if (line.find("STOP") == 0) {
            break;
        } else if (line.find("while") == 0) {
            handle_while_loop_start(line, previous_line, loopInvariants, loopInvariantCounter,
                inWhileLoop, while_measurement_guard, var_is_measure_what_qubit,
                I, measure_to_continue, measure_to_break, verify);
        } else if (line.find("}") == 0) {
            handle_closing_brace(inWhileLoop, inIfBlock, inElseBlock, previous_line, while_measurement_guard,
                I, measure_to_break, measure_to_else, result_after_if, verify);
        } else if (line.find("if") == 0) {
            inIfBlock = true;
            handle_if_block_start(line, previous_line, var_is_measure_what_qubit, measure_to_else);
        } else if (line.find("else") == 0) {
            inElseBlock = true;
            handle_else(measure_to_else);
        } else if (line.find("gate ") == 0) {
            if (line.find("}") == std::string::npos) {
                inGateDef = true; // TODO: unsure if this is necessary
            }
        } else if (line.find("=") != std::string::npos && line.find("measure") != std::string::npos) {
            const std::regex m("([^ ]+) *= *measure.*\\[(\\d+)\\]"); // result = measure problem[4];
            std::sregex_iterator it(line.cbegin(), line.cend(), m);
            if (it == kRegexEnd)
                THROW_AUTOQ_ERROR("Expected measure assignment (var = measure ...[n]) in \"" + line + "\".");
            std::string result = it->str(1);
            int pos = 1 + atoi(it->str(2).c_str());
            var_is_measure_what_qubit[result] = pos;
            // TODO: Actually, we should split the automaton here into two separate copies which
            // are produced from the measurement outcome of 0 and 1, respectively. However, we do
            // not do this for simplicity temporarily.
        }  else {
            single_gate_execute(line, qasm_re, qubit_permutation);
        }
        previous_line = line;
        // print_stats(previous_line, true);
        // print_language(("\n" + previous_line + "\n").c_str());
        stop_execute = std::chrono::steady_clock::now();
    }
    qasm.close();
    return verify;
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::handle_closing_brace(bool& inWhileLoop, bool& inIfBlock, bool& inElseBlock,
    const std::string& previous_line, const std::string& while_measurement_guard,
    Automata<Symbol>& I, Automata<Symbol>& measure_to_break, Automata<Symbol>& measure_to_else,
    Automata<Symbol>& result_after_if, bool& verify) {
    if (inWhileLoop) {
        inWhileLoop = false;
        std::string prev = previous_line;
        std::erase(prev, ' ');
        if (while_measurement_guard != prev)
            THROW_AUTOQ_ERROR("The while loop guard must be repeated at the end of the loop!");
        bool t = this->operator_scaled_inclusion_with_renaming(I);
        verify &= t;
        if (!t) {
            AUTOQ_ERROR("[ERROR] C(measure_to_continue(I)) ⊈ I.");
            fraction_simplification();
            print_language("C(measure_to_continue(I)):\n");
            I.fraction_simplification();
            I.print_language("I:\n");
        }
        *this = measure_to_break;
        gateCount--;
    } else if (inIfBlock) {
        inIfBlock = false;
        result_after_if = *this;
        *this = this->operator||(measure_to_else);
    } else if (inElseBlock) {
        inElseBlock = false;
        *this = this->operator||(result_after_if);
    }
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::handle_while_loop_start(const std::string& line, const std::string& previous_line,
    const std::vector<Automata<Symbol>>& loopInvariants, int& loopInvariantCounter,
    bool& inWhileLoop, std::string& while_measurement_guard,
    const std::map<std::string, int>& var_is_measure_what_qubit,
    Automata<Symbol>& I, Automata<Symbol>& measure_to_continue, Automata<Symbol>& measure_to_break, bool& verify) {
    if (previous_line.find("measure") == std::string::npos)
        THROW_AUTOQ_ERROR("The while loop guard must be a measurement operator.");
    while_measurement_guard = previous_line;
    std::erase(while_measurement_guard, ' ');
    inWhileLoop = true;
    const std::regex varR("\\((.*)\\)");
    std::sregex_iterator it(line.cbegin(), line.cend(), varR);
    if (it == kRegexEnd)
        THROW_AUTOQ_ERROR("Invalid while guard: expected (var) in \"" + line + "\".");
    std::string var = AUTOQ::String::trim(it->str(1));
    bool negate = (var.at(0) == '!');
    if (negate)
        var = var.substr(1);
    int pos = var_is_measure_what_qubit.at(var);
    I = loopInvariants[loopInvariantCounter++];
    this->remove_useless();
    this->reduce();
    I.remove_useless();
    I.reduce();
    bool t = (*this <<= I);
    verify &= t;
    if (!t) {
        AUTOQ_ERROR("[ERROR] C(P) ⊈ I.");
        fraction_simplification();
        print_language("C(P):\n");
        I.fraction_simplification();
        I.print_language("I:\n");
    }
    if (negate) {
        measure_to_continue = I.measure(pos, false);
        measure_to_break = I.measure(pos, true);
    } else {
        measure_to_continue = I.measure(pos, true);
        measure_to_break = I.measure(pos, false);
    }
    *this = measure_to_continue;
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::handle_if_block_start(const std::string& line, const std::string& previous_line,
    const std::map<std::string, int>& var_is_measure_what_qubit,
    Automata<Symbol>& measure_to_else) {
    if (previous_line.find("measure") == std::string::npos)
        THROW_AUTOQ_ERROR("The if guard must be a measurement operator.");
    const std::regex varR("\\((.*)\\)");
    std::sregex_iterator it(line.cbegin(), line.cend(), varR);
    if (it == kRegexEnd)
        THROW_AUTOQ_ERROR("Invalid if guard: expected (var) in \"" + line + "\".");
    std::string var = AUTOQ::String::trim(it->str(1));
    bool negate = (var.at(0) == '!');
    if (negate)
        var = var.substr(1);
    int pos = var_is_measure_what_qubit.at(var);
    if (negate) {
        measure_to_else = this->measure(pos, true);
        *this = this->measure(pos, false);
    } else {
        measure_to_else = this->measure(pos, false);
        *this = this->measure(pos, true);
    }
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::handle_else(const Automata<Symbol>& measure_to_else) {
    *this = measure_to_else;
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::single_gate_execute(const std::string& line, const AUTOQ::QasmRegexes& re, const std::vector<int>& qubit_permutation) {
    std::smatch match_rx;
    std::regex_search(line, match_rx, re.rx);
    std::smatch match_rz;
    std::regex_search(line, match_rz, re.rz);

    // Regex-based gates
    if (match_rx.size() == 3) {
        Rx(AUTOQ::Parsing::parse_angle_to_rational(match_rx[1].str(), "rx", "(1/2)"),
           1 + qubit_permutation[atoi(match_rx[2].str().c_str())]);
        return;
    }
    if (match_rz.size() == 3) {
        Rz(AUTOQ::Parsing::parse_angle_to_rational(match_rz[1].str(), "rz", "(1/2)"),
           1 + qubit_permutation[atoi(match_rz[2].str().c_str())]);
        return;
    }
    if (line.find("ry(pi/2) ") == 0 || line.find("ry(pi / 2)") == 0) {
        std::vector<int> pos = parse_qubit_indices(line, re, qubit_permutation);
        Ry(pos[1]);
        return;
    }

    // Prefix dispatch table: (check, handler)
    using Handler = std::function<void()>;
    std::vector<std::pair<std::function<bool()>, Handler>> table = {
        {[&]{ return line.find("x ") == 0; }, [&]{ X(first_qubit_index(line, re, qubit_permutation)); }},
        {[&]{ return line.find("y ") == 0; }, [&]{ Y(first_qubit_index(line, re, qubit_permutation)); }},
        {[&]{ return line.find("z ") == 0; }, [&]{ Z(first_qubit_index(line, re, qubit_permutation)); }},
        {[&]{ return line.find("h ") == 0; }, [&]{ H(first_qubit_index(line, re, qubit_permutation)); }},
        {[&]{ return line.find("s ") == 0; }, [&]{ S(first_qubit_index(line, re, qubit_permutation)); }},
        {[&]{ return line.find("sdg ") == 0; }, [&]{ Sdg(first_qubit_index(line, re, qubit_permutation)); }},
        {[&]{ return line.find("t ") == 0; }, [&]{ T(first_qubit_index(line, re, qubit_permutation)); }},
        {[&]{ return line.find("tdg ") == 0; }, [&]{ Tdg(first_qubit_index(line, re, qubit_permutation)); }},
        {[&]{ return line.find("cx ") == 0 || line.find("CX ") == 0; }, [&]{
            auto pos = parse_qubit_indices(line, re, qubit_permutation);
            CX(pos[0], pos[1]);
        }},
        {[&]{ return line.find("cz ") == 0; }, [&]{
            auto pos = parse_qubit_indices(line, re, qubit_permutation);
            CZ(pos[0], pos[1]);
        }},
        {[&]{ return line.find("ck ") == 0; }, [&]{
            auto pos = parse_qubit_indices(line, re, qubit_permutation);
            CK(pos[0], pos[1]);
        }},
        {[&]{ return line.find("ccx ") == 0; }, [&]{
            auto pos = parse_qubit_indices(line, re, qubit_permutation);
            CCX(pos[0], pos[1], pos[2]);
        }},
        {[&]{ return line.find("swap ") == 0; }, [&]{
            auto pos = parse_qubit_indices(line, re, qubit_permutation);
            Swap(pos[0], pos[1]);
        }},
    };

    for (auto& [check, handler] : table) {
        if (check()) { handler(); return; }
    }

    if (line.length() > 0)
        THROW_AUTOQ_ERROR(std::string(EM::kUnsupportedGatePrefix) + line + ".");
}

template <typename Symbol>
std::string AUTOQ::Automata<Symbol>::check_the_invariants_types(const std::string& filename) {
    std::ifstream qasm(filename);
    if (!qasm.is_open()) THROW_AUTOQ_ERROR(std::string(EM::kOpenFilePrefix) + filename + ".");
    std::string line;
    while (getline(qasm, line)) {
        line = AUTOQ::String::trim(line);
        if (line.find("while") == 0) {  // while (!result) { // loop-invariant.hsl
            std::sregex_iterator it2(line.cbegin(), line.cend(), AUTOQ::kTrailingComment);
            std::string dir = (std::filesystem::current_path() / filename).parent_path().string();
            auto invariant = ReadAutomaton(dir + std::string("/") + it2->str(1));
            if (std::holds_alternative<AUTOQ::PredicateAutomata>(invariant)) {
                qasm.close();
                THROW_AUTOQ_ERROR(EM::kLoopInvariantPredicate);
            } else if (std::holds_alternative<AUTOQ::SymbolicAutomata>(invariant)) {
                qasm.close();
                return "Symbolic";
            } else if (std::holds_alternative<AUTOQ::ConcreteAutomata>(invariant)) {
            } else {
                qasm.close();
                THROW_AUTOQ_ERROR(EM::kLoopInvariantType);
            }
        }
    }
    qasm.close();
    return "Concrete";
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;