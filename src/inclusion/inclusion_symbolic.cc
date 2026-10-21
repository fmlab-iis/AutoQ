/**
 * Inclusion checking for Symbolic automata: scaled inclusion, operator<<=.
 */
#include "z3/z3++.h"
#include "autoq/inclusion_common.hh"
#include "autoq/inclusion_build_trans.hh"
#include "autoq/inclusion_bfs.hh"
#include "autoq/util/util.hh"
#include "autoq/util/string.hh"
#include "autoq/inclusion.hh"
#include "autoq/aut_description.hh"
#include <queue>
#include <regex>
#include <sstream>

static bool call_smt_solver(const std::string &var_defs, const std::string &assertion) {
    #ifdef DEFINE_TO_USE_COMMAND_LINE_OTHERWISE_USE_Z3_API
    std::string solver = "z3";
    // std::string solver = "/home/alan23273850/AutoQ/smtrat-static";
    // std::string solver = "/home/alan23273850/AutoQ/yices-2.7.0/bin/yices-smt2";
    std::string smt_input = "bash -c \"" + solver + " <(echo '\n(set-logic NRA)\n" + var_defs + "\n(assert " + assertion + ")(check-sat)')\"";
    // auto start = chrono::steady_clock::now();
    // std::cout << smt_input << "\n";
    std::string result = AUTOQ::Util::ShellCmd(smt_input);
    // std::cout << result << "\n";
    // auto duration = chrono::steady_clock::now() - start;
    // std::cout << AUTOQ::Util::Convert::ToString(duration) << "\n";
    #else
    // std::cout << Z3_get_full_version() << "\n";
    z3::context c;
    z3::solver s(c);
    std::string smt_input = var_defs + "(assert " + assertion + ")";
    // std::cout << smt_input << "\n";
    s.from_string(smt_input.c_str());
    auto result = s.check();
    #endif
    // std::cout << result << "\n";
    #ifdef DEFINE_TO_USE_COMMAND_LINE_OTHERWISE_USE_Z3_API
    if (result == "unsat\n") return false;
    else if (result == "sat\n") return true;
    #else
    if (result == z3::unsat) return false;
    else if (result == z3::sat) return true;
    #endif
    else {
        std::cout << smt_input << "\n";
        std::cout << result << "-\n";
        THROW_AUTOQ_ERROR("The solver Z3 did not correctly return SAT or UNSAT.");
    }
}

namespace {
// Rename variables in automaton's leaf transitions and constraints with a prefix (e.g. "R_" or "Q_").
void rename_symbolic_aut_vars(AUTOQ::SymbolicAutomata& aut, const std::string& prefix) {
    auto transitions2 = aut.transitions;
    for (const auto &tr : transitions2) {
        if (tr.first.symbol().is_leaf()) {
            AUTOQ::Complex::SymbolicComplex complex_new;
            for (const auto &t_c : tr.first.symbol().complex) {
                AUTOQ::Complex::Term term2;
                for (const auto &v_i : t_c.first) {
                    if (aut.vars.contains(v_i.first))
                        term2[prefix + v_i.first] = v_i.second;
                    else
                        term2[v_i.first] = v_i.second;
                }
                complex_new[term2] = t_c.second;
            }
            aut.transitions.erase(tr.first);
            auto trfirst = tr.first;
            trfirst.symbol().complex = complex_new;
            aut.transitions[trfirst] = tr.second;
        }
    }
    for (const auto &var : aut.vars)
        aut.constraints = std::regex_replace(aut.constraints, std::regex("(\\b" + var + "\\b)"), prefix + var);
    std::set<std::string> vars2;
    for (const auto &var : aut.vars)
        vars2.insert(prefix + var);
    aut.vars = vars2;
}

// Build SMT formula for leaf-pair ratio consistency and run solver. Returns true iff SAT (inclusion fails).
using LeafPairsOfVertex = std::set<std::set<std::pair<AUTOQ::Symbol::Symbolic, AUTOQ::Symbol::Symbolic>>>;
bool symbolic_leaf_pairs_smt_is_sat(
    const AUTOQ::SymbolicAutomata& autA,
    const AUTOQ::SymbolicAutomata& autB,
    const LeafPairsOfVertex& leaf_pairs_of_one_new_vertex)
{
    std::set<std::string> Y, Z, Z2;
    for (const auto &leaf_pairs_of_one_new_cell : leaf_pairs_of_one_new_vertex) {
        for (const auto &pair : leaf_pairs_of_one_new_cell) {
            for (const auto &var : pair.first.complex.vars())
                Y.insert(var);
            for (const auto &var : pair.second.complex.vars())
                Z2.insert(var);
        }
    }
    for (const auto &var : autA.vars) {
        if (autA.constraints.find(var) != std::string::npos)
            Y.insert(var);
    }
    for (const auto &var : autB.vars) {
        if (autB.constraints.find(var) != std::string::npos)
            Z2.insert(var);
    }
    for (const auto &var : Z2) {
        if (Y.find(var) == Y.end())
            Z.insert(var);
    }
    std::string define_varA = "(declare-const sqrt2 Real)\n(assert (>= sqrt2 0))\n(assert (= (* sqrt2 sqrt2) 2))\n";
    for (const auto &var : Y)
        define_varA += "(declare-const " + var + " Real)\n";
    define_varA += "\n";
    std::string assertion = std::string("(and \n") +
        autA.constraints + "\n" +
        "(forall (";
    for (const auto &var : Z)
        assertion += "(" + var + " Real)";
    assertion += "(ratioR Real)";
    assertion += "(ratioI Real)";
    assertion += ")\n(or\n";
    assertion += "(not " + autB.constraints + ")\n";
    assertion += "(and (= ratioR 0) (= ratioI 0))\n";
    assertion += "(and ";
    int counter = 0;
    for (const auto &leaf_pairs_of_one_new_cell : leaf_pairs_of_one_new_vertex) {
        assertion += "(or ";
        for (const auto &pair : leaf_pairs_of_one_new_cell) {
            define_varA += "(define-fun E" + std::to_string(counter) + "r () Real " + pair.first.complex.realToSMT() + "); " + (std::ostringstream{} << pair.first).str() + "\n";
            define_varA += "(define-fun E" + std::to_string(counter) + "i () Real " + pair.first.complex.imagToSMT() + "); " + (std::ostringstream{} << pair.first).str() + "\n";
            std::string arguments;
            for (const auto &var : pair.second.complex.vars()) {
                if (Y.find(var) == Y.end()) {
                    arguments += "(" + var + " Real)";
                }
            }
            define_varA += "(define-fun F" + std::to_string(counter) + "r (" + arguments + ") Real " + pair.second.complex.realToSMT() + "); " + (std::ostringstream{} << pair.second).str() + "\n";
            define_varA += "(define-fun F" + std::to_string(counter) + "i (" + arguments + ") Real " + pair.second.complex.imagToSMT() + "); " + (std::ostringstream{} << pair.second).str() + "\n";
            assertion += "(distinct ";
            assertion += "E" + std::to_string(counter) + "r ";
            arguments = "";
            for (const auto &var : pair.second.complex.vars()) {
                if (Y.find(var) == Y.end()) {
                    arguments += " " + var;
                }
            }
            if (arguments.empty())
                assertion += "(- (* ratioR F" + std::to_string(counter) + "r) (* ratioI F" + std::to_string(counter) + "i)))\n";
            else
                assertion += "(- (* ratioR (F" + std::to_string(counter) + "r" + arguments + ")) (* ratioI (F" + std::to_string(counter) + "i" + arguments + "))))\n";
            assertion += "(distinct ";
            assertion += "E" + std::to_string(counter) + "i ";
            if (arguments.empty())
                assertion += "(+ (* ratioR F" + std::to_string(counter) + "i) (* ratioI F" + std::to_string(counter) + "r)))\n";
            else
                assertion += "(+ (* ratioR (F" + std::to_string(counter) + "i" + arguments + ")) (* ratioI (F" + std::to_string(counter) + "r" + arguments + "))))\n";
            counter++;
        }
        assertion += ")\n";
    }
    assertion += ")\n";
    assertion += ")))";
    return call_smt_solver(define_varA, assertion);
}
// Inclusion-search policy for symbolic automata: collect the leaf pairs of
// each successor vertex and, at a leaf vertex, let the SMT solver decide.
struct SymbolicLeafPolicy {
    LeafPairsOfVertex leaf_pairs_of_one_new_vertex;
    void begin_vertex() { leaf_pairs_of_one_new_vertex.clear(); }
    bool leaf_pairs_consistent(const std::set<std::pair<AUTOQ::Symbol::Symbolic, AUTOQ::Symbol::Symbolic>>&) const { return true; }
    void record_feasible(const std::set<std::pair<AUTOQ::Symbol::Symbolic, AUTOQ::Symbol::Symbolic>>& leaf_pairs) {
        leaf_pairs_of_one_new_vertex.insert(leaf_pairs);
    }
    bool leaf_vertex_fails(const AUTOQ::SymbolicAutomata& autA, const AUTOQ::SymbolicAutomata& autB) const {
        return symbolic_leaf_pairs_smt_is_sat(autA, autB, leaf_pairs_of_one_new_vertex);
    }
};

// Prepare autA/autB for scaled inclusion: normalize constraints, add zero amplitude to B, optional variable renaming.
static void prepare_aut_for_scaled_inclusion(AUTOQ::SymbolicAutomata& autA, AUTOQ::SymbolicAutomata& autB, bool renaming) {
    if (AUTOQ::String::trim(autA.constraints).empty()) autA.constraints = "true";
    if (AUTOQ::String::trim(autB.constraints).empty()) autB.constraints = "true";
    autB = autB.operator||(AUTOQ::SymbolicAutomata::zero_amplitude(autB.qubitNum));
    if (renaming) {
        rename_symbolic_aut_vars(autA, "R_");
        rename_symbolic_aut_vars(autB, "Q_");
    }
}

}  // namespace

// -------- Inclusion: Symbolic automata (scaled inclusion) --------
bool scaled_inclusion_with_or_without_renaming(AUTOQ::SymbolicAutomata autA, AUTOQ::SymbolicAutomata autB, bool renaming) {
    prepare_aut_for_scaled_inclusion(autA, autB, renaming);

    auto start_include = std::chrono::steady_clock::now();
    std::vector<std::map<AUTOQ::SymbolicAutomata::SymbolTag, AUTOQ::SymbolicAutomata::StateVector>> transA;
    std::vector<std::map<AUTOQ::SymbolicAutomata::Symbol, std::map<AUTOQ::SymbolicAutomata::Tag, AUTOQ::SymbolicAutomata::StateVector>>> transB;
    AUTOQ::build_inclusion_trans(autA, autB, transA, transB);

    SymbolicLeafPolicy policy;
    bool holds = AUTOQ::inclusion_bfs_holds(autA, autB, transA, transB, policy);
    auto stop_include = std::chrono::steady_clock::now();
    autA.stats_->include_status = AUTOQ::Util::Convert::ToString(stop_include - start_include) + (holds ? "" : " X");
    autA.stats_->total_include_time += stop_include - start_include;
    return holds;
}
template <>
// -------- SymbolicAutomata::operator<<= --------
bool AUTOQ::SymbolicAutomata::operator<<=(AUTOQ::SymbolicAutomata autB) const {
    return scaled_inclusion_with_or_without_renaming(*this, autB, false);
}
template <>
bool AUTOQ::SymbolicAutomata::operator_scaled_inclusion_with_renaming(AUTOQ::SymbolicAutomata autB) const {
    return scaled_inclusion_with_or_without_renaming(*this, autB, true);
}

