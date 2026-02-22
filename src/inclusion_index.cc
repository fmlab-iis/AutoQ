/**
 * Inclusion checking for Index automata (operator<=).
 */
#include "autoq/inclusion.hh"
#include "autoq/inclusion_common.hh"
#include "autoq/util/util.hh"
#include "autoq/aut_description.hh"
#include <queue>

namespace AUTOQ {

bool inclusion_index_compare(const IndexAutomata &autA, const IndexAutomata &autB) {
    auto start_include = std::chrono::steady_clock::now();

    // Preparation: Transform transitions into the new data structure.
    std::vector<std::map<IndexAutomata::SymbolTag, IndexAutomata::StateVector>> transA(autA.stateNum);
    std::vector<std::map<IndexAutomata::Symbol, std::map<IndexAutomata::Tag, IndexAutomata::StateVector>>> transB(autB.stateNum);
    for (const auto &t : autA.transitions) {
        const IndexAutomata::SymbolTag &symbol_tag = t.first;
        for (const auto &out_ins : t.second) {
            const auto &out = out_ins.first;
            const auto &ins = out_ins.second;
            assert(ins.size() == 1); // already assume one (q,fc) corresponds to only one input vector.
            transA[out][symbol_tag] = *(ins.begin());
        }
    }
    for (const auto &t : autB.transitions) {
        const IndexAutomata::SymbolTag &symbol_tag = t.first;
        for (const auto &out_ins : t.second) {
            const auto &out = out_ins.first;
            const auto &ins = out_ins.second;
            assert(ins.size() == 1); // already assume one (q,fc) corresponds to only one input vector.
            transB[out][symbol_tag.symbol()][symbol_tag.tag()] = *(ins.begin());
        }
    }

    // Main Routine: Graph Traversal
    typedef std::map<IndexAutomata::State, IndexAutomata::StateSet> Cell;
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
    }
    // Start the BFS!
    while (!bfs.empty()) {
        vertex = bfs.front();
        bfs.pop();
        // List all possible transition combinations of A in this vertex first!
        std::map<IndexAutomata::State, typename std::map<IndexAutomata::SymbolTag, IndexAutomata::StateVector>::iterator> A_transition_combinations;
        std::map<IndexAutomata::State, std::vector<IndexAutomata::Tag>> possible_colors_for_qA; // Elements may repeat in the vector!
        for (const auto& qA_qBs : *(vertex.begin())) {
            auto qA = qA_qBs.first;
            A_transition_combinations[qA] = transA[qA].begin();
            for (const auto &fc_in : transA[qA]) {
                possible_colors_for_qA[qA].push_back(fc_in.first.tag());
            }
        }
        bool have_listed_all_combinationsA = false;
        do { // Construct one new vertex for each possible combination of A's transitions.
            unsigned all_used_colors = ~0;
            bool color_consistent = true;
            bool is_leaf_vertex = true;
            for (const auto &kv : A_transition_combinations) {
                all_used_colors &= kv.second->first.tag();
                if (kv.second->second.size() > 0)
                    is_leaf_vertex = false;
            }
            color_consistent = (all_used_colors != 0);
            if (color_consistent) {
                Vertex vertex2;
                bool vertex_fail = true; // is_leaf_vertex
                for (const auto &cell : vertex) {
                    Cell cell2;
                    bool cell_fail = false; // is_leaf_vertex
                    bool have_listed_all_combinationsB = false;
                    std::map<IndexAutomata::State, std::map<IndexAutomata::Symbol, std::map<IndexAutomata::Tag, IndexAutomata::StateVector>::iterator>> B_transition_combinations;
                    for (const auto &kv : A_transition_combinations) {
                        const auto &qA = kv.first;
                        const auto &fc_in = *(kv.second);
                        const auto &desired_symbol = fc_in.first.symbol();
                        const auto &inA = fc_in.second;
                        for (const auto &s : inA) {
                            cell2[s];
                        }
                        if (cell.at(qA).empty()) {
                            have_listed_all_combinationsB = true;
                        }
                        for (const auto &qB : cell.at(qA)) {
                            if (transB[qB].find(desired_symbol) == transB[qB].end()) {
                                have_listed_all_combinationsB = true;
                            } else if (!B_transition_combinations[qB].empty() && B_transition_combinations[qB].begin()->first != desired_symbol) {
                                have_listed_all_combinationsB = true;
                            } else {
                                B_transition_combinations[qB][desired_symbol] = transB[qB][desired_symbol].begin();
                            }
                        }
                    }
                    if (have_listed_all_combinationsB) {
                        cell_fail = true;
                        vertex2.insert(cell2);
                    }
                    while (!have_listed_all_combinationsB) {
                        for (auto &kv : cell2) {
                            kv.second.clear();
                        }
                        unsigned all_used_colors = ~0;
                        for (const auto &kv : B_transition_combinations) {
                            all_used_colors &= kv.second.begin()->second->first;
                        }
                        bool color_consistent2 = (all_used_colors != 0);
                        if (color_consistent2) {
                            for (const auto &kv : A_transition_combinations) {
                                const auto &qA = kv.first;
                                const auto &inA = kv.second->second;
                                for (const auto &qB : cell.at(qA)) {
                                    const auto &inB = B_transition_combinations[qB].begin()->second->second;
                                    assert(inA.size() == inB.size());
                                    for (unsigned i=0; i<inA.size(); i++) {
                                        cell2[inA.at(i)].insert(inB.at(i));
                                    }
                                }
                            }
                        }
                        vertex2.insert(cell2);

                        // Increment indices
                        for (auto it = B_transition_combinations.rbegin(); it != B_transition_combinations.rend(); it++) {
                            const auto &q = it->first;
                            const auto &f = it->second.begin()->first;
                            if (std::next(it->second.begin()->second, 1) != transB[q][f].end()) {
                                it->second.begin()->second++;
                                break;
                            } else {
                                if (it == std::prev(B_transition_combinations.rend(), 1)) {
                                    have_listed_all_combinationsB = true;
                                    break;
                                }
                                it->second.begin()->second = transB[q][f].begin();
                            }
                        }
                    }
                    if (!cell_fail) {
                        vertex_fail = false;
                    }
                }
                if (is_leaf_vertex) {
                    if (vertex_fail) {
                        auto stop_include = std::chrono::steady_clock::now();
                        IndexAutomata::include_status = AUTOQ::Util::Convert::ToString(stop_include - start_include) + " X";
                        IndexAutomata::total_include_time += stop_include - start_include;
                        return false;
                    }
                } else if (created.contains(vertex2)) {
                } else {
                    created.insert(vertex2);
                    bfs.push(vertex2);
                }
            }

            // Increment indices
            for (auto it = A_transition_combinations.rbegin(); it != A_transition_combinations.rend(); it++) {
                const auto &qA = it->first;
                if (std::next(it->second, 1) != transA[qA].end()) {
                    it->second = std::next(it->second, 1);
                    break;
                } else {
                    if (it == std::prev(A_transition_combinations.rend(), 1)) {
                        have_listed_all_combinationsA = true;
                        break;
                    }
                    it->second = transA[qA].begin();
                }
            }
        } while (!have_listed_all_combinationsA);
    }
    auto stop_include = std::chrono::steady_clock::now();
    IndexAutomata::include_status = AUTOQ::Util::Convert::ToString(stop_include - start_include);
    IndexAutomata::total_include_time += stop_include - start_include;
    return true;
}

} // namespace AUTOQ

template <>
bool AUTOQ::Automata<AUTOQ::Symbol::Index>::operator<=(const Automata<AUTOQ::Symbol::Index> &autB) const {
    return AUTOQ::inclusion_index_compare(*this, autB);
}
