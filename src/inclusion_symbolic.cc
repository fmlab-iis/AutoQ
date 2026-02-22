/**
 * Inclusion checking for Symbolic automata: check_validity, scaled inclusion, operator<<=.
 */
#include "z3/z3++.h"
#include "autoq/inclusion_common.hh"
#include "autoq/util/util.hh"
#include "autoq/util/string.hh"
#include "autoq/inclusion.hh"
#include "autoq/aut_description.hh"
#include <queue>
#include <sstream>
bool AUTOQ::check_validity(Constraint C, const PredicateAutomata::Symbol &ps, const SymbolicAutomata::Symbol &te) {
    std::string str(ps);
    /* Replace all real(.) in C.content with .R and
       replace all imag(.) in C.content with .I */
    str = std::regex_replace(str, std::regex("real\\((.*?)\\)"), "$1R");
    str = std::regex_replace(str, std::regex("imag\\((.*?)\\)"), "$1I");
    /******************************************************************/
    auto regToExpr = C.to_exprs(te);
    for (const auto &kv : regToExpr) // example: z3 <(echo '(declare-fun x () Int)(declare-fun z () Int)(assert (= z (+ x 3)))(check-sat)')
        str = std::regex_replace(str, std::regex(kv.first), kv.second);
    // std::cout << std::string(C) + "(assert (not " + str + "))(check-sat)\n";

    #if 1
    // std::cout << Z3_get_full_version() << "\n";
    z3::context c;
    z3::solver s(c);
    s.from_string((std::string(C) + "(assert (not " + str + "))").c_str());
    auto result = s.check();
    // std::cout << result << "\n";
    if (result == z3::unsat) return true;
    else if (result == z3::sat) return false;
    #else
    std::string smt_input = "bash -c \"z3 <(echo '" + std::string(C) + "(assert (not " + str + "))(check-sat)')\"";
    // auto startSim = chrono::steady_clock::now();
    auto result = AUTOQ::Util::ShellCmd(smt_input);
    // std::cout << smt_input << "\n";
    // std::cout << result << "\n";
    // auto durationSim = chrono::steady_clock::now() - startSim;
    // std::cout << toString2(durationSim) << "\n";
    if (result == "unsat\n") return true;
    else if (result == "sat\n") return false;
    #endif
    else {
        std::cout << std::string(C) << "\n";
        std::cout << str << "\n";
        std::cout << result << "-\n";
        THROW_AUTOQ_ERROR("The solver Z3 did not correctly return SAT or UNSAT.\nIt's probably because the specification automaton is NOT a predicate automaton.");
    }
}

// [removed ~320 lines of commented SymbolicAutomata<=PredicateAutomata operator - see git history if needed]

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
    // std::cout << AUTOQ::Util::print_duration(duration) << "\n";
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

using SymbolicTransA = std::vector<std::map<AUTOQ::SymbolicAutomata::SymbolTag, AUTOQ::SymbolicAutomata::StateVector>>;
using SymbolicTransB = std::vector<std::map<AUTOQ::SymbolicAutomata::Symbol, std::map<AUTOQ::SymbolicAutomata::Tag, AUTOQ::SymbolicAutomata::StateVector>>>;
void build_symbolic_trans(const AUTOQ::SymbolicAutomata& autA, const AUTOQ::SymbolicAutomata& autB,
                          SymbolicTransA& transA, SymbolicTransB& transB) {
    transA.resize(autA.stateNum);
    transB.resize(autB.stateNum);
    for (const auto &t : autA.transitions) {
        const auto &symbol_tag = t.first;
        for (const auto &out_ins : t.second) {
            const auto &out = out_ins.first;
            const auto &ins = out_ins.second;
            assert(ins.size() == 1);
            transA[out][symbol_tag] = *(ins.begin());
        }
    }
    for (const auto &t : autB.transitions) {
        const auto &symbol_tag = t.first;
        for (const auto &out_ins : t.second) {
            const auto &out = out_ins.first;
            const auto &ins = out_ins.second;
            assert(ins.size() == 1);
            transB[out][symbol_tag.symbol()][symbol_tag.tag()] = *(ins.begin());
        }
    }
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
}  // namespace

// -------- Inclusion: Symbolic automata (scaled inclusion) --------
bool scaled_inclusion_with_or_without_renaming(AUTOQ::SymbolicAutomata autA, AUTOQ::SymbolicAutomata autB, bool renaming) {
    if (AUTOQ::String::trim(autA.constraints).empty()) autA.constraints = "true";
    if (AUTOQ::String::trim(autB.constraints).empty()) autB.constraints = "true";
    autB = autB.operator||(AUTOQ::SymbolicAutomata::zero_amplitude(autB.qubitNum));

    if (renaming) {
        rename_symbolic_aut_vars(autA, "R_");
        rename_symbolic_aut_vars(autB, "Q_");
    }

    auto start_include = std::chrono::steady_clock::now();

    SymbolicTransA transA;
    SymbolicTransB transB;
    build_symbolic_trans(autA, autB, transA, transB);

    // Main Routine: Graph Traversal
    typedef std::map<AUTOQ::SymbolicAutomata::State, AUTOQ::SymbolicAutomata::StateSet> Cell;
    typedef std::set<Cell> Vertex;
    std::set<Vertex> created; // Remember created configurations.
    std::queue<Vertex> bfs; // the queue used for traversing the graph
    Vertex vertex; // current vertex data structure
    // Construct source vertices.
    for (const auto &qA : autA.finalStates) {
        vertex = Vertex();
        for (const auto &qB : autB.finalStates) {
            vertex.insert(Cell({{qA, {qB}}}));
        }
        assert(!created.contains(vertex));
        created.insert(vertex);
        bfs.push(vertex);
        INCLUSION_DEBUG("CREATE SOURCE VERTEX: " << AUTOQ::Util::Convert::ToString(vertex));
    }
    // Start the BFS!
    while (!bfs.empty()) {
        vertex = bfs.front();
        INCLUSION_DEBUG("EXTRACT VERTEX: " << AUTOQ::Util::Convert::ToString(vertex));
        bfs.pop();
        // List all possible transition combinations of A in this vertex first!
        std::map<AUTOQ::SymbolicAutomata::State, typename std::map<AUTOQ::SymbolicAutomata::SymbolTag, AUTOQ::SymbolicAutomata::StateVector>::iterator> A_transition_combinations;
        std::map<AUTOQ::SymbolicAutomata::State, std::vector<AUTOQ::SymbolicAutomata::Tag>> possible_colors_for_qA; // Elements may repeat in the vector!
        for (const auto& qA_qBs : *(vertex.begin())) {
            auto qA = qA_qBs.first;
            A_transition_combinations[qA] = transA[qA].begin();
            for (const auto &fc_in : transA[qA]) {
                possible_colors_for_qA[qA].push_back(fc_in.first.tag());
            }
        }
        bool have_listed_all_combinationsA = false;
        do { // Construct one new vertex for each possible combination of A's transitions.
            /************************************************************/
            // Check if the current combination is color-consistent.
            // If not, skip this one and continue to the next combination.
            unsigned all_used_colors = ~0;
            bool color_consistent = true;
            // Check if there is no any children state derived from the current combination.
            // If it is true, then we shall not create new vertices derived from this one,
            // and we shall judge whether the inclusion does not hold right now.
            bool is_leaf_vertex = true;
            INCLUSION_DEBUG("A's CURRENTLY CONSIDERED TRANSITIONS: ");
            for (const auto &kv : A_transition_combinations) { // Print the current combination
                INCLUSION_DEBUG(AUTOQ::Util::Convert::ToString(kv.second->first)
                              + AUTOQ::Util::Convert::ToString(kv.second->second)
                              + " -> " + AUTOQ::Util::Convert::ToString(kv.first));
                all_used_colors &= kv.second->first.tag();
                if (kv.second->second.size() > 0)
                    is_leaf_vertex = false;
            }
            color_consistent = (all_used_colors != 0);
            // for (const auto &qA_c : possible_colors_for_qA) { // for each fixed qA
            //     int counter = 0;
            //     for (const auto &color : qA_c.second) { // loop through all possible colors
            //         if ((color | all_used_colors) == all_used_colors) { // color is a subset of all_used_colors
            //             counter++;
            //             if (counter >= 2) {
            //                 color_consistent = false;
            //                 break;
            //             }
            //         }
            //     }
            // }
            /*************************************************************************/
            // Only pick this combination of A's transitions if it is color-consistent.
            INCLUSION_DEBUG("ARE " << (color_consistent ? "" : "NOT ") << "COLOR-CONSISTENT.");
            if (color_consistent) {
                Vertex vertex2;
                bool vertex_fail = true; // is_leaf_vertex
                std::set<std::set<std::pair<AUTOQ::Symbol::Symbolic, AUTOQ::Symbol::Symbolic>>> leaf_pairs_of_one_new_vertex;
                for (const auto &cell : vertex) {
                    INCLUSION_DEBUG("EXTRACT CELL: " << AUTOQ::Util::Convert::ToString(cell));
                    Cell cell2;
                    bool cell_fail = false; // is_leaf_vertex
                    bool have_listed_all_combinationsB = false;
                    // std::map<SymbolicAutomata::State, std::vector<SymbolicAutomata::Tag>> possible_colors_for_qB;

                    // The following loop is used to build all possible transition combinations of B,
                    // given the cell (set) of constraints, each of which describes "some A's state <==> some B's states".
                    std::map<AUTOQ::SymbolicAutomata::State, std::set<AUTOQ::Symbol::Symbolic>> As_symbols_associated_with_Bs_states;
                    std::map<AUTOQ::SymbolicAutomata::State, std::map<AUTOQ::SymbolicAutomata::Symbol, std::map<AUTOQ::SymbolicAutomata::Tag, AUTOQ::SymbolicAutomata::StateVector>::iterator>> B_transition_combinations_data;
                    std::map<AUTOQ::SymbolicAutomata::State, AUTOQ::SymbolicAutomata::Symbol> B_transition_combinations;
                    for (const auto &kv : A_transition_combinations) { // simply loop through all qA's in this cell
                        const auto &qA = kv.first;
                        const auto &fc_in = *(kv.second); // the currently picked transition for qA
                        const auto &desired_symbol = fc_in.first.symbol(); // the corresponding symbol
                        const auto &inA = fc_in.second; // the current input vector for qA
                        for (const auto &s : inA) {
                            cell2[s]; // Leave room for B's states for each A's child state.
                        }
                        if (cell.at(qA).empty()) {
                            // If qB has no states corresponding to qA,
                            // simply construct the unique cell without B's states!
                            have_listed_all_combinationsB = true;
                            // Do NOT use break; here to avoid interrupting
                            // the process of building cell2 completely.
                        }
                        for (const auto &qB : cell.at(qA)) {
                            As_symbols_associated_with_Bs_states[qB].insert(desired_symbol);
                            /****** Build all possible colors for qB *******/
                            // IMPORTANT: Each qB can only be processed once; otherwise the number
                            // of some colors recorded in possible_colors_for_qB[qB] will be wrong!
                            // if (possible_colors_for_qB.find(qB) == possible_colors_for_qB.end()) {
                            //     for (const auto &f_cin : transB[qB]) {
                            //         for (const auto &c_in : f_cin.second) {
                            //             possible_colors_for_qB[qB].push_back(c_in.first);
                            //         }
                            //     }
                            // }
                            /***********************************************/
                            if (desired_symbol.is_internal()) {
                                AUTOQ::SymbolicAutomata::Symbol desired_symbol2(desired_symbol.qubit());
                                if (transB[qB].find(desired_symbol2) == transB[qB].end()) {
                                    // If qB has no transitions with the desired symbol,
                                    // simply construct the unique cell without B's states!
                                    have_listed_all_combinationsB = true;
                                    // Do NOT use break; here to avoid interrupting
                                    // the process of building cell2 completely.
                                } else if (!B_transition_combinations_data[qB].empty() && B_transition_combinations_data[qB].begin()->first != desired_symbol2) {
                                    // If qB is enforced to take two different symbols together,
                                    // simply construct the unique cell without B's states!
                                    have_listed_all_combinationsB = true;
                                    // Do NOT use break; here to avoid interrupting
                                    // the process of building cell2 completely.
                                } else {
                                    B_transition_combinations_data[qB][desired_symbol2] = transB[qB][desired_symbol2].begin();
                                }
                            } else { // if (desired_symbol.is_leaf()) {
                                for (const auto &predicate_v : transB[qB]) {
                                    const auto &predicate = predicate_v.first;
                                    B_transition_combinations_data[qB][predicate] = transB[qB][predicate].begin();
                                }
                            }
                            if (B_transition_combinations_data[qB].empty()) {
                                have_listed_all_combinationsB = true;
                            }
                        }
                        // Do NOT use break; here to avoid interrupting
                        // the process of building cell2 completely.
                    }
                    if (have_listed_all_combinationsB) { // No possible combination exists!
                        cell_fail = true; // is_leaf_vertex
                        vertex2.insert(cell2);
                        INCLUSION_DEBUG("PUSH CELL: " << AUTOQ::Util::Convert::ToString(cell2) << " TO THE NEW VERTEX.");
                    } else {
                        for (const auto &kv : B_transition_combinations_data) {
                            assert(!kv.second.empty());
                            B_transition_combinations[kv.first] = kv.second.begin()->first;
                        }
                    } // mutually exclusive with the following loop
                    bool at_least_one_feasible_combination_in_the_following_while_loop = false;
                    while (!have_listed_all_combinationsB) { // Construct one new cell for each possible combination of B's transitions.
                        for (auto &kv : cell2) { // Initialize the current cell.
                            kv.second.clear();
                        }
                        /*************************************************************/
                        // Check if the current combination is color-consistent.
                        // If not, simply construct the unique cell without B's states!
                        unsigned all_used_colors = ~0;
                        INCLUSION_DEBUG("B's CURRENTLY CONSIDERED TRANSITIONS: ");
                        std::set<std::pair<AUTOQ::Symbol::Symbolic, AUTOQ::Symbol::Symbolic>> leaf_pairs_of_one_new_cell;
                        for (const auto &kv : B_transition_combinations) { // Print the current combination
                            INCLUSION_DEBUG(AUTOQ::Util::Convert::ToString(kv.second)
                                + "[" + AUTOQ::Util::Convert::ToString(B_transition_combinations_data.at(kv.first).at(kv.second)->first) + "]"
                                + AUTOQ::Util::Convert::ToString(B_transition_combinations_data.at(kv.first).at(kv.second)->second)
                                + " -> " + AUTOQ::Util::Convert::ToString(kv.first));
                            all_used_colors &= B_transition_combinations_data.at(kv.first).at(kv.second)->first;
                            for (const auto &desired_symbol : As_symbols_associated_with_Bs_states.at(kv.first))
                                leaf_pairs_of_one_new_cell.insert({desired_symbol, kv.second});
                        }
                        bool color_consistent2 = (all_used_colors != 0);
                        /*****************************************/
                        // for (const auto &qB_c : possible_colors_for_qB) { // for each fixed qB
                        //     int counter = 0;
                        //     for (const auto &color : qB_c.second) { // loop through all possible colors
                        //         if ((color | all_used_colors) == all_used_colors) { // color is a subset of all_used_colors
                        //             counter++;
                        //             if (counter >= 2) {
                        //                 color_consistent2 = false;
                        //                 break;
                        //             }
                        //         }
                        //     }
                        //     if (!color_consistent2)
                        //         break; // shortcut
                        // }
                        /*************************************************************/
                        INCLUSION_DEBUG("ARE " << (color_consistent2 ? "" : "NOT ") << "COLOR-CONSISTENT.");
                        // If consistent, equivalize the two input vectors of each equivalent transition pair.
                        if (color_consistent2) {
                            leaf_pairs_of_one_new_vertex.insert(leaf_pairs_of_one_new_cell);
                            at_least_one_feasible_combination_in_the_following_while_loop = true;
                            for (const auto &kv : A_transition_combinations) {
                                const auto &qA = kv.first;
                                const auto &inA = kv.second->second; // the current input vector for qA
                                for (const auto &qB : cell.at(qA)) {
                                    const auto &inB = B_transition_combinations_data.at(qB).at(B_transition_combinations.at(qB))->second; // the current input vector for qB
                                    assert(inA.size() == inB.size()); // one function symbol has only one arity.
                                    for (unsigned i=0; i<inA.size(); i++) {
                                        cell2[inA.at(i)].insert(inB.at(i));
                                    }
                                }
                            }
                        }
                        vertex2.insert(cell2);
                        INCLUSION_DEBUG("PUSH CELL: " << AUTOQ::Util::Convert::ToString(cell2) << " TO THE NEW VERTEX.");

                        // Increment indices
                        for (auto it = B_transition_combinations.rbegin(); it != B_transition_combinations.rend(); it++) {
                            // std::cout << AUTOQ::Util::Convert::ToString(*(it->second.begin()->second.second)) << "\n";
                            // std::cout << AUTOQ::Util::Convert::ToString(*std::prev(it->second.begin()->second.first.end(), 1)) << "\n";
                            // std::cout << AUTOQ::Util::Convert::ToString(it->second.begin()->second.second) << "\n";
                            // std::cout << &*(it->second.begin()->second.second) << "\n";
                            // std::cout << &*std::next(it->second.begin()->second.second, 1) << "\n";
                            // std::cout << &*(it->second.begin()->second.first.end()) << "\n";
                            const auto &q = it->first;
                            const auto &f = it->second;
                            if (std::next(B_transition_combinations_data.at(q).at(f), 1) != transB[q][f].end()) {
                                B_transition_combinations_data.at(q).at(f)++;
                                break;
                            } else {
                                B_transition_combinations_data.at(q).at(f) = transB[q][f].begin();
                                auto it2 = std::next(B_transition_combinations_data.at(q).find(f));
                                if (it2 != B_transition_combinations_data.at(q).end()) {
                                    it->second = it2->first;
                                    break;
                                } else {
                                    it->second = B_transition_combinations_data.at(q).begin()->first;
                                    if (it == std::prev(B_transition_combinations.rend(), 1)) { // position equivalent to .begin()
                                        have_listed_all_combinationsB = true;
                                        break; // All combinations have been generated
                                    }
                                }
                            }
                        }
                    }
                    if (!at_least_one_feasible_combination_in_the_following_while_loop) { // No possible combination exists!
                        cell_fail = true; // is_leaf_vertex
                    }
                    if (!cell_fail) { // is_leaf_vertex
                        vertex_fail = false;
                    }
                }
                if (is_leaf_vertex) { // only when considering some particular transitions
                    INCLUSION_DEBUG("THE VERTEX: " << AUTOQ::Util::Convert::ToString(vertex2) << " LEADS A TO NOTHING OF STATES, SO WE SHALL NOT PUSH THIS VERTEX BUT CHECK IF B HAS POSSIBLE SIMULTANEOUS TRANSITION COMBINATIONS LEADING TO THIS VERTEX.");
                    if (vertex_fail) {
                        auto stop_include = std::chrono::steady_clock::now();
                        AUTOQ::SymbolicAutomata::include_status = AUTOQ::Util::Convert::ToString(stop_include - start_include) + " X";
                        INCLUSION_DEBUG("UNFORTUNATELY B HAS NO POSSIBLE TRANSITION COMBINATIONS, SO THE INCLUSION DOES NOT HOLD :(");
                        AUTOQ::SymbolicAutomata::total_include_time += stop_include - start_include;
                        return false;
                    }
                    if (symbolic_leaf_pairs_smt_is_sat(autA, autB, leaf_pairs_of_one_new_vertex)) {
                        auto stop_include = std::chrono::steady_clock::now();
                        AUTOQ::SymbolicAutomata::include_status = AUTOQ::Util::Convert::ToString(stop_include - start_include) + " X";
                        INCLUSION_DEBUG("UNFORTUNATELY B HAS NO POSSIBLE TRANSITION COMBINATIONS, SO THE INCLUSION DOES NOT HOLD :(");
                        AUTOQ::SymbolicAutomata::total_include_time += stop_include - start_include;
                        return false;
                    }
                } else if (created.contains(vertex2)) {
                    INCLUSION_DEBUG("THE VERTEX: " << AUTOQ::Util::Convert::ToString(vertex2) << " HAS BEEN CREATED BEFORE.");
                } else {
                    created.insert(vertex2);
                    bfs.push(vertex2);
                    INCLUSION_DEBUG("BUILD EDGE: " << AUTOQ::Util::Convert::ToString(vertex) << " -> " << AUTOQ::Util::Convert::ToString(vertex2));
                }
            }

            // Increment indices
            for (auto it = A_transition_combinations.rbegin(); it != A_transition_combinations.rend(); it++) {
                const auto &qA = it->first;
                if (std::next(it->second, 1) != transA[qA].end()) {
                    it->second = std::next(it->second, 1);
                    break;
                } else {
                    if (it == std::prev(A_transition_combinations.rend(), 1)) { // position equivalent to .begin()
                        have_listed_all_combinationsA = true;
                        break; // All combinations have been generated
                    }
                    it->second = transA[qA].begin();
                }
            }
        } while (!have_listed_all_combinationsA);
    }
    auto stop_include = std::chrono::steady_clock::now();
    AUTOQ::SymbolicAutomata::include_status = AUTOQ::Util::Convert::ToString(stop_include - start_include);
    INCLUSION_DEBUG("FORTUNATELY FOR EACH (MAXIMAL) PATH B HAS POSSIBLE SIMULTANEOUS TRANSITION COMBINATIONS, SO THE INCLUSION DOES HOLD :)");
    AUTOQ::SymbolicAutomata::total_include_time += stop_include - start_include;
    return true;
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

