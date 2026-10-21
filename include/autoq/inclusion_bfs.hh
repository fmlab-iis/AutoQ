#ifndef _AUTOQ_INCLUSION_BFS_HH_
#define _AUTOQ_INCLUSION_BFS_HH_

/**
 * The graph search shared by the Concrete and Symbolic inclusion checks.
 *
 * A vertex is a set of cells; a cell maps each state of A to the set of
 * states of B that must accept the same trees. The search enumerates the
 * combinations of A's transitions and, for each, the combinations of B's
 * transitions that can follow them.
 *
 * The parts that differ between the variants are delegated to LeafPolicy:
 *   void begin_vertex();                          // a new successor vertex is started
 *   bool leaf_pairs_consistent(const LeafPairs&); // extra check on a combination of B's transitions
 *   void record_feasible(const LeafPairs&);       // a consistent combination was found
 *   bool leaf_vertex_fails(const Aut&, const Aut&); // decide a leaf vertex that B can follow
 * where LeafPairs is std::set<std::pair<Symbol, Symbol>> (A's leaf symbol, B's leaf symbol).
 */
#include <map>
#include <queue>
#include <set>
#include <vector>
#include "autoq/inclusion_common.hh"
#include "autoq/aut_description.hh"

namespace AUTOQ {

template <typename Symbol, typename LeafPolicy>
bool inclusion_bfs_holds(
    const AUTOQ::Automata<Symbol>& autA,
    const AUTOQ::Automata<Symbol>& autB,
    std::vector<std::map<typename AUTOQ::Automata<Symbol>::SymbolTag, typename AUTOQ::Automata<Symbol>::StateVector>>& transA,
    std::vector<std::map<Symbol, std::map<typename AUTOQ::Automata<Symbol>::Tag, typename AUTOQ::Automata<Symbol>::StateVector>>>& transB,
    LeafPolicy& policy)
{
    using Aut = AUTOQ::Automata<Symbol>;
    // Main Routine: Graph Traversal
    typedef std::map<typename Aut::State, typename Aut::StateSet> Cell;
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
        std::map<typename Aut::State, typename std::map<typename Aut::SymbolTag, typename Aut::StateVector>::iterator> A_transition_combinations;
        for (const auto& qA_qBs : *(vertex.begin())) {
            auto qA = qA_qBs.first;
            A_transition_combinations[qA] = transA[qA].begin();
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
            /*************************************************************************/
            // Only pick this combination of A's transitions if it is color-consistent.
            INCLUSION_DEBUG("ARE " << (color_consistent ? "" : "NOT ") << "COLOR-CONSISTENT.");
            if (color_consistent) {
                Vertex vertex2;
                bool vertex_fail = true; // is_leaf_vertex
                policy.begin_vertex();
                for (const auto &cell : vertex) {
                    INCLUSION_DEBUG("EXTRACT CELL: " << AUTOQ::Util::Convert::ToString(cell));
                    Cell cell2;
                    bool cell_fail = false; // is_leaf_vertex
                    bool have_listed_all_combinationsB = false;

                    // The following loop is used to build all possible transition combinations of B,
                    // given the cell (set) of constraints, each of which describes "some A's state <==> some B's states".
                    std::map<typename Aut::State, std::set<Symbol>> As_symbols_associated_with_Bs_states;
                    std::map<typename Aut::State, std::map<typename Aut::Symbol, typename std::map<typename Aut::Tag, typename Aut::StateVector>::iterator>> B_transition_combinations_data;
                    std::map<typename Aut::State, typename Aut::Symbol> B_transition_combinations;
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
                            if (desired_symbol.is_internal()) {
                                typename Aut::Symbol desired_symbol2(desired_symbol.qubit());
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
                        std::set<std::pair<Symbol, Symbol>> leaf_pairs_of_one_new_cell;
                        for (const auto &kv : B_transition_combinations) { // Print the current combination
                            INCLUSION_DEBUG(AUTOQ::Util::Convert::ToString(kv.second)
                                + "[" + AUTOQ::Util::Convert::ToString(B_transition_combinations_data.at(kv.first).at(kv.second)->first) + "]"
                                + AUTOQ::Util::Convert::ToString(B_transition_combinations_data.at(kv.first).at(kv.second)->second)
                                + " -> " + AUTOQ::Util::Convert::ToString(kv.first));
                            all_used_colors &= B_transition_combinations_data.at(kv.first).at(kv.second)->first;
                            for (const auto &desired_symbol : As_symbols_associated_with_Bs_states.at(kv.first))
                                leaf_pairs_of_one_new_cell.insert({desired_symbol, kv.second});
                        }
                        bool color_consistent2 = (all_used_colors != 0) && policy.leaf_pairs_consistent(leaf_pairs_of_one_new_cell);
                        /*****************************************/
                        /*************************************************************/
                        INCLUSION_DEBUG("ARE " << (color_consistent2 ? "" : "NOT ") << "COLOR-CONSISTENT.");
                        // If consistent, equivalize the two input vectors of each equivalent transition pair.
                        if (color_consistent2) {
                            policy.record_feasible(leaf_pairs_of_one_new_cell);
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
                        INCLUSION_DEBUG("UNFORTUNATELY B HAS NO POSSIBLE TRANSITION COMBINATIONS, SO THE INCLUSION DOES NOT HOLD :(");
                        return false;
                    }
                    if (policy.leaf_vertex_fails(autA, autB)) {
                        INCLUSION_DEBUG("UNFORTUNATELY B HAS NO POSSIBLE TRANSITION COMBINATIONS, SO THE INCLUSION DOES NOT HOLD :(");
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
    INCLUSION_DEBUG("FORTUNATELY FOR EACH (MAXIMAL) PATH B HAS POSSIBLE SIMULTANEOUS TRANSITION COMBINATIONS, SO THE INCLUSION DOES HOLD :)");
    return true;
}

}  // namespace AUTOQ

#endif
