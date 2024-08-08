#include "autoq/util/util.hh"
#include "autoq/inclusion.hh"
#include "autoq/aut_description.hh"
#include <queue>

template <typename Symbol>
bool AUTOQ::Automata<Symbol>::operator<=(const Automata<Symbol> &autB) const requires concrete_like<Symbol> {
    // migrate instance variables
    Automata<AUTOQ::Symbol::Index> aut1;
    aut1.name = this->name;
    aut1.finalStates = this->finalStates;
    aut1.stateNum = this->stateNum;
    aut1.qubitNum = this->qubitNum;
    // aut1.transitions = this->transitions;
    aut1.isTopdownDeterministic = this->isTopdownDeterministic;
    Automata<AUTOQ::Symbol::Index> aut2;
    aut2.name = autB.name;
    aut2.finalStates = autB.finalStates;
    aut2.stateNum = autB.stateNum;
    aut2.qubitNum = autB.qubitNum;
    // aut2.transitions = autB.transitions;
    aut2.isTopdownDeterministic = autB.isTopdownDeterministic;
    // migrate static variables
    Automata<AUTOQ::Symbol::Index>::gateCount = Automata<Symbol>::gateCount;
    Automata<AUTOQ::Symbol::Index>::stateBefore = Automata<Symbol>::stateBefore;
    Automata<AUTOQ::Symbol::Index>::transitionBefore = Automata<Symbol>::transitionBefore;
    Automata<AUTOQ::Symbol::Index>::gateLog = Automata<Symbol>::gateLog;
    Automata<AUTOQ::Symbol::Index>::opLog = Automata<Symbol>::opLog;
    Automata<AUTOQ::Symbol::Index>::include_status = Automata<Symbol>::include_status;
    Automata<AUTOQ::Symbol::Index>::binop_time = Automata<Symbol>::binop_time;
    Automata<AUTOQ::Symbol::Index>::branch_rest_time = Automata<Symbol>::branch_rest_time;
    Automata<AUTOQ::Symbol::Index>::value_rest_time = Automata<Symbol>::value_rest_time;
    Automata<AUTOQ::Symbol::Index>::total_gate_time = Automata<Symbol>::total_gate_time;
    Automata<AUTOQ::Symbol::Index>::total_removeuseless_time = Automata<Symbol>::total_removeuseless_time;
    Automata<AUTOQ::Symbol::Index>::total_reduce_time = Automata<Symbol>::total_reduce_time;
    Automata<AUTOQ::Symbol::Index>::total_include_time = Automata<Symbol>::total_include_time;
    Automata<AUTOQ::Symbol::Index>::start_execute = Automata<Symbol>::start_execute;
    Automata<AUTOQ::Symbol::Index>::stop_execute = Automata<Symbol>::stop_execute;
    // migrate transitions
    std::vector<Symbol> symbol_map;
    for (const auto &t : this->transitions) {
        const auto &symbol_tag = t.first;
        const auto &symbol = symbol_tag.symbol();
        int i = 0;
        for (; i<=symbol_map.size(); i++) {
            if (i == symbol_map.size()) {
                symbol_map.push_back(symbol);
            }
            if (i == symbol_map.size() || symbol_map.at(i).valueEqual(symbol)) {
                Automata<AUTOQ::Symbol::Index>::SymbolTag symbol_tag2 = {AUTOQ::Symbol::Index(symbol.is_leaf(), i), symbol_tag.tag()};
                for (const auto &out_ins : t.second) {
                    const auto &out = out_ins.first;
                    const auto &ins = out_ins.second;
                    for (const auto &in : ins)
                        aut1.transitions[symbol_tag2][out].insert(in);
                }
                break;
            }
        }
    }
    for (const auto &t : autB.transitions) {
        const auto &symbol_tag = t.first;
        const auto &symbol = symbol_tag.symbol();
        int i = 0;
        for (; i<=symbol_map.size(); i++) {
            if (i == symbol_map.size()) {
                symbol_map.push_back(symbol);
            }
            if (i == symbol_map.size() || symbol_map.at(i).valueEqual(symbol)) {
                Automata<AUTOQ::Symbol::Index>::SymbolTag symbol_tag2 = {AUTOQ::Symbol::Index(symbol.is_leaf(), i), symbol_tag.tag()};
                for (const auto &out_ins : t.second) {
                    const auto &out = out_ins.first;
                    const auto &ins = out_ins.second;
                    for (const auto &in : ins)
                        aut2.transitions[symbol_tag2][out].insert(in);
                }
                break;
            }
        }
    }
    // main routine
    bool result = aut1 <= aut2;
    // migrate static variables
    Automata<Symbol>::gateCount = Automata<AUTOQ::Symbol::Index>::gateCount;
    Automata<Symbol>::stateBefore = Automata<AUTOQ::Symbol::Index>::stateBefore;
    Automata<Symbol>::transitionBefore = Automata<AUTOQ::Symbol::Index>::transitionBefore;
    Automata<Symbol>::gateLog = Automata<AUTOQ::Symbol::Index>::gateLog;
    Automata<Symbol>::opLog = Automata<AUTOQ::Symbol::Index>::opLog;
    Automata<Symbol>::include_status = Automata<AUTOQ::Symbol::Index>::include_status;
    Automata<Symbol>::binop_time = Automata<AUTOQ::Symbol::Index>::binop_time;
    Automata<Symbol>::branch_rest_time = Automata<AUTOQ::Symbol::Index>::branch_rest_time;
    Automata<Symbol>::value_rest_time = Automata<AUTOQ::Symbol::Index>::value_rest_time;
    Automata<Symbol>::total_gate_time = Automata<AUTOQ::Symbol::Index>::total_gate_time;
    Automata<Symbol>::total_removeuseless_time = Automata<AUTOQ::Symbol::Index>::total_removeuseless_time;
    Automata<Symbol>::total_reduce_time = Automata<AUTOQ::Symbol::Index>::total_reduce_time;
    Automata<Symbol>::total_include_time = Automata<AUTOQ::Symbol::Index>::total_include_time;
    Automata<Symbol>::start_execute = Automata<AUTOQ::Symbol::Index>::start_execute;
    Automata<Symbol>::stop_execute = Automata<AUTOQ::Symbol::Index>::stop_execute;
    return result;
}

template <>
bool AUTOQ::Automata<AUTOQ::Symbol::Index>::operator<=(const Automata<AUTOQ::Symbol::Index> &autB) const {
    auto start_include = std::chrono::steady_clock::now();

    // Preparation: Transform transitions into the new data structure.
    std::vector<std::map<SymbolTag, StateVector>> transA(this->stateNum);
    std::vector<std::map<Symbol, std::map<Tag, StateVector>>> transB(autB.stateNum);
    for (const auto &t : this->transitions) {
        const SymbolTag &symbol_tag = t.first;
        for (const auto &out_ins : t.second) {
            const auto &out = out_ins.first;
            const auto &ins = out_ins.second;
            assert(ins.size() == 1); // already assume one (q,fc) corresponds to only one input vector.
            transA[out][symbol_tag] = *(ins.begin());
        }
    }
    for (const auto &t : autB.transitions) {
        const SymbolTag &symbol_tag = t.first;
        for (const auto &out_ins : t.second) {
            const auto &out = out_ins.first;
            const auto &ins = out_ins.second;
            assert(ins.size() == 1); // already assume one (q,fc) corresponds to only one input vector.
            transB[out][symbol_tag.symbol()][symbol_tag.tag()] = *(ins.begin());
        }
    }
    // this->print_aut("autA\n");
    // autB.print_aut("autB\n");

    // Main Routine: Graph Traversal
    typedef std::map<State, StateSet> Cell;
    typedef std::set<Cell> Vertex;
    std::set<Vertex> created; // Remember created configurations.
    std::queue<Vertex> bfs; // the queue used for traversing the graph
    Vertex vertex; // current vertex data structure
    // Construct source vertices.
    for (const auto &qA : this->finalStates) {
        vertex = Vertex();
        for (const auto &qB : autB.finalStates) {
            vertex.insert(Cell({{qA, {qB}}}));
        }
        assert(!created.contains(vertex));
        created.insert(vertex);
        bfs.push(vertex);
        // AUTOQ_DEBUG("CREATE SOURCE VERTEX: " << AUTOQ::Util::Convert::ToString(vertex));
    }
    // Start the BFS!
    while (!bfs.empty()) {
        vertex = bfs.front();
        // AUTOQ_DEBUG("EXTRACT VERTEX: " << AUTOQ::Util::Convert::ToString(vertex));
        bfs.pop();
        // List all possible transition combinations of A in this vertex first!
        std::map<State, typename std::map<SymbolTag, StateVector>::iterator> A_transition_combinations;
        std::map<State, std::vector<Tag>> possible_colors_for_qA; // Elements may repeat in the vector!
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
            // AUTOQ_DEBUG("A's CURRENTLY CONSIDERED TRANSITIONS: ");
            for (const auto &kv : A_transition_combinations) { // Print the current combination
                // AUTOQ_DEBUG(AUTOQ::Util::Convert::ToString(kv.second->first)
                //         + AUTOQ::Util::Convert::ToString(kv.second->second)
                //         + " -> " + AUTOQ::Util::Convert::ToString(kv.first));
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
            // AUTOQ_DEBUG("ARE " << (color_consistent ? "" : "NOT ") << "COLOR-CONSISTENT.");
            if (color_consistent) {
                Vertex vertex2;
                bool vertex_fail = true; // is_leaf_vertex
                for (const auto &cell : vertex) {
                    // AUTOQ_DEBUG("EXTRACT CELL: " << AUTOQ::Util::Convert::ToString(cell));
                    Cell cell2;
                    bool cell_fail = false; // is_leaf_vertex
                    bool have_listed_all_combinationsB = false;
                    // std::map<State, std::vector<Tag>> possible_colors_for_qB;

                    // The following loop is used to build all possible transition combinations of B,
                    // given the cell (set) of constraints, each of which describes "some A's state <==> some B's states".
                    std::map<State, std::map<Symbol, std::map<Tag, StateVector>::iterator>> B_transition_combinations;
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
                            if (transB[qB].find(desired_symbol) == transB[qB].end()) {
                                // If qB has no transitions with the desired symbol,
                                // simply construct the unique cell without B's states!
                                have_listed_all_combinationsB = true;
                                // Do NOT use break; here to avoid interrupting
                                // the process of building cell2 completely.
                            } else if (!B_transition_combinations[qB].empty() && B_transition_combinations[qB].begin()->first != desired_symbol) {
                                // If qB is enforced to take two different symbols together,
                                // simply construct the unique cell without B's states!
                                have_listed_all_combinationsB = true;
                                // Do NOT use break; here to avoid interrupting
                                // the process of building cell2 completely.
                            } else {
                                B_transition_combinations[qB][desired_symbol] = transB[qB][desired_symbol].begin();
                            }
                        }
                        // Do NOT use break; here to avoid interrupting
                        // the process of building cell2 completely.
                    }
                    if (have_listed_all_combinationsB) { // No possible combination exists!
                        cell_fail = true; // is_leaf_vertex
                        vertex2.insert(cell2);
                        // AUTOQ_DEBUG("PUSH CELL: " << AUTOQ::Util::Convert::ToString(cell2) << " TO THE NEW VERTEX.");
                    } // mutually exclusive with the following loop
                    while (!have_listed_all_combinationsB) { // Construct one new cell for each possible combination of B's transitions.
                        for (auto &kv : cell2) { // Initialize the current cell.
                            kv.second.clear();
                        }
                        /*************************************************************/
                        // Check if the current combination is color-consistent.
                        // If not, simply construct the unique cell without B's states!
                        bool color_consistent2 = true;
                        unsigned all_used_colors = ~0;
                        // AUTOQ_DEBUG("B's CURRENTLY CONSIDERED TRANSITIONS: ");
                        for (const auto &kv : B_transition_combinations) { // Print the current combination
                            // AUTOQ_DEBUG(AUTOQ::Util::Convert::ToString(kv.second.begin()->first)
                            //     + "[" + AUTOQ::Util::Convert::ToString(kv.second.begin()->second->first) + "]"
                            //     + AUTOQ::Util::Convert::ToString(kv.second.begin()->second->second)
                            //     + " -> " + AUTOQ::Util::Convert::ToString(kv.first));
                            all_used_colors &= kv.second.begin()->second->first;
                        }
                        color_consistent2 = (all_used_colors != 0);
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
                        // AUTOQ_DEBUG("ARE " << (color_consistent2 ? "" : "NOT ") << "COLOR-CONSISTENT.");
                        // If consistent, equivalize the two input vectors of each equivalent transition pair.
                        if (color_consistent2) {
                            for (const auto &kv : A_transition_combinations) {
                                const auto &qA = kv.first;
                                const auto &inA = kv.second->second; // the current input vector for qA
                                for (const auto &qB : cell.at(qA)) {
                                    const auto &inB = B_transition_combinations[qB].begin()->second->second; // the current input vector for qB
                                    assert(inA.size() == inB.size()); // one function symbol has only one arity.
                                    for (unsigned i=0; i<inA.size(); i++) {
                                        cell2[inA.at(i)].insert(inB.at(i));
                                    }
                                }
                            }
                        }
                        vertex2.insert(cell2);
                        // AUTOQ_DEBUG("PUSH CELL: " << AUTOQ::Util::Convert::ToString(cell2) << " TO THE NEW VERTEX.");

                        // Increment indices
                        for (auto it = B_transition_combinations.rbegin(); it != B_transition_combinations.rend(); it++) {
                            // std::cout << AUTOQ::Util::Convert::ToString(*(it->second.begin()->second.second)) << "\n";
                            // std::cout << AUTOQ::Util::Convert::ToString(*std::prev(it->second.begin()->second.first.end(), 1)) << "\n";
                            // std::cout << AUTOQ::Util::Convert::ToString(it->second.begin()->second.second) << "\n";
                            // std::cout << &*(it->second.begin()->second.second) << "\n";
                            // std::cout << &*std::next(it->second.begin()->second.second, 1) << "\n";
                            // std::cout << &*(it->second.begin()->second.first.end()) << "\n";
                            const auto &q = it->first;
                            const auto &f = it->second.begin()->first;
                            if (std::next(it->second.begin()->second, 1) != transB[q][f].end()) {
                                it->second.begin()->second++;
                                break;
                            } else {
                                if (it == std::prev(B_transition_combinations.rend(), 1)) { // position equivalent to .begin()
                                    have_listed_all_combinationsB = true;
                                    break; // All combinations have been generated
                                }
                                it->second.begin()->second = transB[q][f].begin();
                            }
                        }
                    }
                    if (!cell_fail) { // is_leaf_vertex
                        vertex_fail = false;
                    }
                }
                if (is_leaf_vertex) { // only when considering some particular transitions
                    // AUTOQ_DEBUG("THE VERTEX: " << AUTOQ::Util::Convert::ToString(vertex2) << " LEADS A TO NOTHING OF STATES, SO WE SHALL NOT PUSH THIS VERTEX BUT CHECK IF B HAS POSSIBLE SIMULTANEOUS TRANSITION COMBINATIONS LEADING TO THIS VERTEX.");
                    if (vertex_fail) {
                        auto stop_include = std::chrono::steady_clock::now();
                        include_status = AUTOQ::Util::Convert::toString(stop_include - start_include) + " X";
                        // AUTOQ_DEBUG("UNFORTUNATELY B HAS NO POSSIBLE TRANSITION COMBINATIONS, SO THE INCLUSION DOES NOT HOLD :(");
                        total_include_time += stop_include - start_include;
                        return false;
                    }
                } else if (created.contains(vertex2)) {
                    // AUTOQ_DEBUG("THE VERTEX: " << AUTOQ::Util::Convert::ToString(vertex2) << " HAS BEEN CREATED BEFORE.");
                } else {
                    created.insert(vertex2);
                    bfs.push(vertex2);
                    // AUTOQ_DEBUG("BUILD EDGE: " << AUTOQ::Util::Convert::ToString(vertex) << " -> " << AUTOQ::Util::Convert::ToString(vertex2));
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
    include_status = AUTOQ::Util::Convert::toString(stop_include - start_include);
    // AUTOQ_DEBUG("FORTUNATELY FOR EACH (MAXIMAL) PATH B HAS POSSIBLE SIMULTANEOUS TRANSITION COMBINATIONS, SO THE INCLUSION DOES HOLD :)");
    total_include_time += stop_include - start_include;
    return true;
}

bool AUTOQ::check_validity(Constraint C, const PredicateAutomata::Symbol &ps, const SymbolicAutomata::Symbol &te) {
    std::string str(ps);
    auto regToExpr = C.to_exprs(te);
    for (const auto &kv : regToExpr) // example: z3 <(echo '(declare-fun x () Int)(declare-fun z () Int)(assert (= z (+ x 3)))(check-sat)')
        str = std::regex_replace(str, std::regex(kv.first), kv.second);
    // std::cout << std::string(C) + "(assert (not " + str + "))(check-sat)\n";
    std::string smt_input = "bash -c \"z3 <(echo '" + std::string(C) + "(assert (not " + str + "))(check-sat)')\"";
    // auto startSim = chrono::steady_clock::now();
    AUTOQ::Util::ShellCmd(smt_input, str);
    // std::cout << smt_input << "\n";
    // std::cout << str << "\n";
    // auto durationSim = chrono::steady_clock::now() - startSim;
    // std::cout << toString2(durationSim) << "\n";
    if (str == "unsat\n") return true;
    else if (str == "sat\n") return false;
    else {
        std::cout << smt_input << "\n";
        std::cout << str << "-\n";
        throw std::runtime_error("[ERROR] The solver Z3 did not correctly return SAT or UNSAT.\nIt's probably because the specification automaton is NOT a predicate automaton.");
    }
}

bool AUTOQ::check_inclusion(const Constraint &C, SymbolicAutomata autA, PredicateAutomata autB) {
    autA.fraction_simplification();
    // autB.fraction_simplification();
    auto start_include = std::chrono::steady_clock::now();

    // Preparation: Transform transitions into the new data structure.
    std::vector<std::map<SymbolicAutomata::SymbolTag, SymbolicAutomata::StateVector>> transA(autA.stateNum);
    std::vector<std::map<PredicateAutomata::Symbol, std::map<PredicateAutomata::Tag, PredicateAutomata::StateVector>>> transB(autB.stateNum);
    for (const auto &t : autA.transitions) {
        const auto &symbol_tag = t.first;
        for (const auto &out_ins : t.second) {
            const auto &out = out_ins.first;
            const auto &ins = out_ins.second;
            assert(ins.size() == 1); // already assume one (q,fc) corresponds to only one input vector.
            transA[out][symbol_tag] = *(ins.begin());
        }
    }
    for (const auto &t : autB.transitions) {
        const auto &symbol_tag = t.first;
        for (const auto &out_ins : t.second) {
            const auto &out = out_ins.first;
            const auto &ins = out_ins.second;
            assert(ins.size() == 1); // already assume one (q,fc) corresponds to only one input vector.
            transB[out][symbol_tag.symbol()][symbol_tag.tag()] = *(ins.begin());
        }
    }
    // autA.print_aut("autA\n");
    // autB.print_aut("autB\n");

    // Main Routine: Graph Traversal
    typedef std::map<SymbolicAutomata::State, PredicateAutomata::StateSet> Cell;
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
        // AUTOQ_DEBUG("CREATE SOURCE VERTEX: " << AUTOQ::Util::Convert::ToString(vertex));
    }
    // Start the BFS!
    while (!bfs.empty()) {
        vertex = bfs.front();
        // AUTOQ_DEBUG("EXTRACT VERTEX: " << AUTOQ::Util::Convert::ToString(vertex));
        bfs.pop();
        // List all possible transition combinations of A in this vertex first!
        std::map<SymbolicAutomata::State, typename std::map<SymbolicAutomata::SymbolTag, SymbolicAutomata::StateVector>::iterator> A_transition_combinations;
        std::map<SymbolicAutomata::State, std::vector<SymbolicAutomata::Tag>> possible_colors_for_qA; // Elements may repeat in the vector!
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
            // AUTOQ_DEBUG("A's CURRENTLY CONSIDERED TRANSITIONS: ");
            for (const auto &kv : A_transition_combinations) { // Print the current combination
                // AUTOQ_DEBUG(AUTOQ::Util::Convert::ToString(kv.second->first)
                //         + AUTOQ::Util::Convert::ToString(kv.second->second)
                //         + " -> " + AUTOQ::Util::Convert::ToString(kv.first));
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
            // AUTOQ_DEBUG("ARE " << (color_consistent ? "" : "NOT ") << "COLOR-CONSISTENT.");
            if (color_consistent) {
                Vertex vertex2;
                bool vertex_fail = true; // is_leaf_vertex
                for (const auto &cell : vertex) {
                    // AUTOQ_DEBUG("EXTRACT CELL: " << AUTOQ::Util::Convert::ToString(cell));
                    Cell cell2;
                    bool cell_fail = false; // is_leaf_vertex
                    bool have_listed_all_combinationsB = false;
                    // std::map<PredicateAutomata::State, std::vector<PredicateAutomata::Tag>> possible_colors_for_qB;

                    // The following loop is used to build all possible transition combinations of B,
                    // given the cell (set) of constraints, each of which describes "some A's state <==> some B's states".
                    std::map<PredicateAutomata::State, std::map<PredicateAutomata::Symbol, std::map<PredicateAutomata::Tag, PredicateAutomata::StateVector>::iterator>> B_transition_combinations_data;
                    std::map<PredicateAutomata::State, PredicateAutomata::Symbol> B_transition_combinations;
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
                                PredicateAutomata::Symbol desired_symbol2(desired_symbol.qubit());
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
                                if (B_transition_combinations_data[qB].empty()) {
                                    for (const auto &predicate_v : transB[qB]) {
                                        const auto &predicate = predicate_v.first;
                                        if (check_validity(C, predicate, desired_symbol)) { // C ⇒ predicate(desired_symbol)
                                            B_transition_combinations_data[qB][predicate] = transB[qB][predicate].begin();
                                        }
                                    }
                                } else {
                                    const auto copy = B_transition_combinations_data[qB];
                                    for (const auto &predicate_v : copy) {
                                        const auto &predicate = predicate_v.first;
                                        if (!check_validity(C, predicate, desired_symbol)) { // C ⇒ predicate(desired_symbol)
                                            B_transition_combinations_data[qB].erase(predicate);
                                        }
                                    }
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
                        // AUTOQ_DEBUG("PUSH CELL: " << AUTOQ::Util::Convert::ToString(cell2) << " TO THE NEW VERTEX.");
                    } else {
                        for (const auto &kv : B_transition_combinations_data) {
                            assert(!kv.second.empty());
                            B_transition_combinations[kv.first] = kv.second.begin()->first;
                        }
                    } // mutually exclusive with the following loop
                    while (!have_listed_all_combinationsB) { // Construct one new cell for each possible combination of B's transitions.
                        for (auto &kv : cell2) { // Initialize the current cell.
                            kv.second.clear();
                        }
                        /*************************************************************/
                        // Check if the current combination is color-consistent.
                        // If not, simply construct the unique cell without B's states!
                        bool color_consistent2 = true;
                        unsigned all_used_colors = ~0;
                        // AUTOQ_DEBUG("B's CURRENTLY CONSIDERED TRANSITIONS: ");
                        for (const auto &kv : B_transition_combinations) { // Print the current combination
                            // AUTOQ_DEBUG(AUTOQ::Util::Convert::ToString(kv.second)
                            //     + "[" + AUTOQ::Util::Convert::ToString(B_transition_combinations_data.at(kv.first).at(kv.second)->first) + "]"
                            //     + AUTOQ::Util::Convert::ToString(B_transition_combinations_data.at(kv.first).at(kv.second)->second)
                            //     + " -> " + AUTOQ::Util::Convert::ToString(kv.first));
                            all_used_colors &= B_transition_combinations_data.at(kv.first).at(kv.second)->first;
                        }
                        color_consistent2 = (all_used_colors != 0);
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
                        // AUTOQ_DEBUG("ARE " << (color_consistent2 ? "" : "NOT ") << "COLOR-CONSISTENT.");
                        // If consistent, equivalize the two input vectors of each equivalent transition pair.
                        if (color_consistent2) {
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
                        // AUTOQ_DEBUG("PUSH CELL: " << AUTOQ::Util::Convert::ToString(cell2) << " TO THE NEW VERTEX.");

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
                    if (!cell_fail) { // is_leaf_vertex
                        vertex_fail = false;
                    }
                }
                if (is_leaf_vertex) { // only when considering some particular transitions
                    // AUTOQ_DEBUG("THE VERTEX: " << AUTOQ::Util::Convert::ToString(vertex2) << " LEADS A TO NOTHING OF STATES, SO WE SHALL NOT PUSH THIS VERTEX BUT CHECK IF B HAS POSSIBLE SIMULTANEOUS TRANSITION COMBINATIONS LEADING TO THIS VERTEX.");
                    if (vertex_fail) {
                        auto stop_include = std::chrono::steady_clock::now();
                        SymbolicAutomata::include_status = AUTOQ::Util::Convert::toString(stop_include - start_include) + " X";
                        // AUTOQ_DEBUG("UNFORTUNATELY B HAS NO POSSIBLE TRANSITION COMBINATIONS, SO THE INCLUSION DOES NOT HOLD :(");
                        SymbolicAutomata::total_include_time += stop_include - start_include;
                        return false;
                    }
                } else if (created.contains(vertex2)) {
                    // AUTOQ_DEBUG("THE VERTEX: " << AUTOQ::Util::Convert::ToString(vertex2) << " HAS BEEN CREATED BEFORE.");
                } else {
                    created.insert(vertex2);
                    bfs.push(vertex2);
                    // AUTOQ_DEBUG("BUILD EDGE: " << AUTOQ::Util::Convert::ToString(vertex) << " -> " << AUTOQ::Util::Convert::ToString(vertex2));
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
    SymbolicAutomata::include_status = AUTOQ::Util::Convert::toString(stop_include - start_include);
    // AUTOQ_DEBUG("FORTUNATELY FOR EACH (MAXIMAL) PATH B HAS POSSIBLE SIMULTANEOUS TRANSITION COMBINATIONS, SO THE INCLUSION DOES HOLD :)");
    SymbolicAutomata::total_include_time += stop_include - start_include;
    return true;
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;