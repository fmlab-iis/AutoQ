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
        unsigned i = 0;
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
        unsigned i = 0;
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
    /* Replace all real(.) in C.content with .R and
       replace all imag(.) in C.content with .I */
    str = std::regex_replace(str, std::regex("real\\((.*?)\\)"), "$1R");
    str = std::regex_replace(str, std::regex("imag\\((.*?)\\)"), "$1I");
    /******************************************************************/
    auto regToExpr = C.to_exprs(te);
    for (const auto &kv : regToExpr) // example: z3 <(echo '(declare-fun x () Int)(declare-fun z () Int)(assert (= z (+ x 3)))(check-sat)')
        str = std::regex_replace(str, std::regex(kv.first), kv.second);
    // std::cout << std::string(C) + "(assert (not " + str + "))(check-sat)\n";
    std::string smt_input = "bash -c \"z3 <(echo '" + std::string(C) + "(assert (not " + str + "))(check-sat)')\"";
    // auto startSim = chrono::steady_clock::now();
    str = AUTOQ::Util::ShellCmd(smt_input);
    // std::cout << smt_input << "\n";
    // std::cout << str << "\n";
    // auto durationSim = chrono::steady_clock::now() - startSim;
    // std::cout << toString2(durationSim) << "\n";
    if (str == "unsat\n") return true;
    else if (str == "sat\n") return false;
    else {
        std::cout << smt_input << "\n";
        std::cout << str << "-\n";
        THROW_AUTOQ_ERROR("The solver Z3 did not correctly return SAT or UNSAT.\nIt's probably because the specification automaton is NOT a predicate automaton.");
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

// #define MIN

// template <typename Symbol>
// bool AUTOQ::Automata<Symbol>::operator<=(const Automata<Symbol> &Q) const {
//     using State = Automata<Symbol>::State;
//     using StateSet = Automata<Symbol>::StateSet;
//     StateSet As_finalStates(Q.finalStates.begin(), Q.finalStates.end());
//     std::map<State, std::set<StateSet>> processed; // Line 1: ← ∅;
//     std::map<State, std::set<StateSet>> worklist;

//     Automata<Symbol>::BottomUpTransitions R_transitions;
//     for (const auto &t : this->transitions) {
//         const auto &symbol_tag = t.first;
//         for (const auto &out_ins : t.second) {
//             auto s = out_ins.first;
//             for (const auto &in : out_ins.second)
//                 R_transitions[symbol_tag][in].insert(s);
//         }
//     }
//     Automata<Symbol>::BottomUpTransitions Q_transitions;
//     for (const auto &t : Q.transitions) {
//         const auto &symbol_tag = t.first;
//         for (const auto &out_ins : t.second) {
//             auto s = out_ins.first;
//             for (const auto &in : out_ins.second)
//                 Q_transitions[symbol_tag][in].insert(s);
//         }
//     }

//     /************************************/
//     // Line 2-4: Construct the initial worklist!
//     for (const auto &tr : R_transitions) {
//         if (tr.first.is_leaf()) {
//             auto vr = tr.first;
//             vr.symbol().fraction_simplification();
//             for (const auto &sr : tr.second.at({})) {
//                 StateSet Uq;
//                 for (const auto &tq : Q_transitions) {
//                     if (tq.first.is_leaf()) {
//                         auto vq = tq.first;
//                         vq.symbol().fraction_simplification();
//                         // if (cr.valueEqual(cq)) {
//                         if (vr == vq) {
//                             for (const auto &uq : tq.second.at({})) {
//                                 Uq.insert(uq);
//                             }
//                         }
//                     }
//                 }

//                 #ifdef MIN
//                 auto copy = worklist[sr]; // Min{...}
//                 for (const auto &t : copy) {
//                     if (std::includes(t.begin(), t.end(), Uq.begin(), Uq.end()))
//                         worklist[sr].erase(t);
//                 }
//                 bool cancel = false;
//                 for (const auto &t : worklist[sr]) {
//                     if (std::includes(Uq.begin(), Uq.end(), t.begin(), t.end())) {
//                         cancel = true;
//                         break;
//                     }
//                 }
//                 if (!cancel)
//                 #endif
//                     worklist[sr].insert(Uq);
//             }
//         }
//     }
//     /************************************/
//     while (!worklist.empty()) { // Line 5
//         /*********************************************/
//         // Line 6
//         auto it = worklist.begin(); // const auto &it ?
//         if (it->second.empty()) {
//             worklist.erase(it);
//             continue;
//         }
//         auto sr = it->first;
//         auto Uq = *(it->second.begin());
//         it->second.erase(it->second.begin());
//         /*********************************************/
//         // Line 7
//         if (this->finalStates.contains(sr)) {
//             StateSet ss;
//             for (const auto &uq : Uq) {
//                 ss.insert(uq);
//             }
//             std::set<int> intersection; // Create a set to store the intersection
//             std::set_intersection( // Use set_intersection to find the common elements
//                 ss.begin(), ss.end(),
//                 Q.finalStates.begin(), Q.finalStates.end(),
//                 std::inserter(intersection, intersection.begin())
//             );
//             if (intersection.empty()) { // Check if the intersection is empty
//                 return false;
//             }
//         }
//         /*********************************************/
//         // Line 8
//         #ifdef MIN
//         auto copy = processed[sr]; // Min{...}
//         for (const auto &t : copy) {
//             if (std::includes(t.begin(), t.end(), Uq.begin(), Uq.end()))
//                 processed[sr].erase(t);
//         }
//         bool cancel = false;
//         for (const auto &t : processed[sr]) {
//             if (std::includes(Uq.begin(), Uq.end(), t.begin(), t.end())) {
//                 cancel = true;
//                 break;
//             }
//         }
//         if (!cancel)
//         #endif
//             processed[sr].insert(Uq);
//         // std::cout << AUTOQ::Util::Convert::ToString(processed) << "\n";
//         /*********************************************/
//         // Line 10
//         auto sr1 = sr;
//         const auto &Uq1 = Uq;
//         for (const auto &kv : processed) {
//             auto sr2 = kv.first;
//             for (const auto &Uq2 : kv.second) {
//                 for (const auto &tr : R_transitions) {
//                     const auto &alpha = tr.first;
//                     /*********************************************/
//                     // Line 11
//                     auto Hr_ptr = tr.second.find({sr1, sr2});
//                     if (Hr_ptr == tr.second.end()) continue;
//                     StateSet Hr = Hr_ptr->second;
//                     if (Hr.empty()) continue;
//                     /*********************************************/
//                     StateSet Uq_; // Line 12
//                     /*********************************************/
//                     // Line 13
//                     for (const auto &sq1 : Uq1) {
//                         for (const auto &sq2 : Uq2) {
//                             /*********************************************/
//                             // Line 15
//                             StateSet sqSet;
//                             auto it = Q_transitions.find(alpha);
//                             if (it != Q_transitions.end()) {
//                                 auto ptr = it->second.find({sq1, sq2});
//                                 if (ptr == it->second.end()) continue;
//                                 sqSet = ptr->second;
//                             }
//                             if (sqSet.empty()) continue;
//                             /*********************************************/
//                             // Line 16
//                             for (const auto &sq : sqSet) {
//                                 Uq_.insert(sq);
//                             }
//                             /*********************************************/
//                         }
//                     }
//                     /*********************************************/
//                     // Line 17-18
//                     for (const auto &sr_ : Hr) {
//                         if (!processed[sr_].contains(Uq_) && !worklist[sr_].contains(Uq_)) {
//                             #ifdef MIN
//                             auto copy = worklist[sr_]; // Min{...}
//                             for (const auto &t : copy) {
//                                 if (std::includes(t.begin(), t.end(), Uq_.begin(), Uq_.end()))
//                                     worklist[sr_].erase(t);
//                             }
//                             bool cancel = false;
//                             for (const auto &t : worklist[sr_]) {
//                                 if (std::includes(Uq_.begin(), Uq_.end(), t.begin(), t.end())) {
//                                     cancel = true;
//                                     break;
//                                 }
//                             }
//                             if (!cancel)
//                             #endif
//                                 worklist[sr_].insert(Uq_);
//                         }
//                     }
//                     /*********************************************/
//                 }
//             }
//         }
//         auto sr2 = sr;
//         const auto &Uq2 = Uq;
//         for (const auto &kv : processed) {
//             auto sr1 = kv.first;
//             for (const auto &Uq1 : kv.second) {
//                 if (sr1 == sr2 && Uq1 == Uq2) continue;
//                 for (const auto &tr : R_transitions) {
//                     const auto &alpha = tr.first;
//                     /*********************************************/
//                     // Line 11
//                     auto Hr_ptr = tr.second.find({sr1, sr2});
//                     if (Hr_ptr == tr.second.end()) continue;
//                     StateSet Hr = Hr_ptr->second;
//                     if (Hr.empty()) continue;
//                     /*********************************************/
//                     StateSet Uq_; // Line 12
//                     /*********************************************/
//                     // Line 13
//                     for (const auto &sq1 : Uq1) {
//                         for (const auto &sq2 : Uq2) {
//                             /*********************************************/
//                             // Line 15
//                             StateSet sqSet;
//                             auto it = Q_transitions.find(alpha);
//                             if (it != Q_transitions.end()) {
//                                 auto ptr = it->second.find({sq1, sq2});
//                                 if (ptr == it->second.end()) continue;
//                                 sqSet = ptr->second;
//                             }
//                             if (sqSet.empty()) continue;
//                             /*********************************************/
//                             // Line 16
//                             for (const auto &sq : sqSet) {
//                                 Uq_.insert(sq);
//                             }
//                             /*********************************************/
//                         }
//                     }
//                     /*********************************************/
//                     // Line 17-18
//                     for (const auto &sr_ : Hr) {
//                         if (!processed[sr_].contains(Uq_) && !worklist[sr_].contains(Uq_)) {
//                             #ifdef MIN
//                             auto copy = worklist[sr_]; // Min{...}
//                             for (const auto &t : copy) {
//                                 if (std::includes(t.begin(), t.end(), Uq_.begin(), Uq_.end()))
//                                     worklist[sr_].erase(t);
//                             }
//                             bool cancel = false;
//                             for (const auto &t : worklist[sr_]) {
//                                 if (std::includes(Uq_.begin(), Uq_.end(), t.begin(), t.end())) {
//                                     cancel = true;
//                                     break;
//                                 }
//                             }
//                             if (!cancel)
//                             #endif
//                                 worklist[sr_].insert(Uq_);
//                         }
//                     }
//                     /*********************************************/
//                 }
//             }
//         }
//     }
//     return true;
// }

// bool call_smt_solver(const std::string &var_defs, const std::string &assertion) {
//     std::string smt_input = "bash -c \"z3 <(echo '" + var_defs + "(assert " + assertion + ")(check-sat)')\"";
//     // auto start = chrono::steady_clock::now();
//     // std::cout << smt_input << "\n";
//     // std::string result = ShellCmd(smt_input);
//     // std::cout << result << "\n";
//     // auto duration = chrono::steady_clock::now() - start;
//     // std::cout << AUTOQ::Util::print_duration(duration) << "\n";

//     // std::cout << Z3_get_full_version() << "\n";
//     z3::context c;
//     z3::solver s(c);
//     s.from_string((var_defs + "(assert " + assertion + ")").c_str());
//     auto result = s.check();
//     // std::cout << result << "\n";
//     if (result == z3::unsat) return false;
//     else if (result == z3::sat) return true;
//     else {
//         std::cout << smt_input << "\n";
//         std::cout << result << "-\n";
//         THROW_AUTOQ_ERROR("The solver Z3 did not correctly return SAT or UNSAT.");
//     }
// }

// struct PairComparator {
//     bool operator()(const std::pair<AUTOQ::TreeAutomata::State, std::pair<AUTOQ::Complex::Complex, AUTOQ::Complex::Complex>> &lhs, const std::pair<AUTOQ::TreeAutomata::State, std::pair<AUTOQ::Complex::Complex, AUTOQ::Complex::Complex>> &rhs) const {
//         auto lhsS = lhs.first;
//         auto rhsS = rhs.first;
//         auto lhsC = lhs.second;
//         auto rhsC = rhs.second;
//         return !(lhsS == rhsS && (
//             (lhsC.first.isZero() && rhsC.first.isZero()) ||
//             (!lhsC.first.isZero() && !rhsC.first.isZero() && (lhsC.first * rhsC.second).valueEqual(lhsC.second * rhsC.first))
//         ));
//     }
// };
// template <>
// bool AUTOQ::TreeAutomata::operator<<=(TreeAutomata Q) const {
//     Q = Q.operator||(AUTOQ::TreeAutomata::zero_amplitude(Q.qubitNum));

//     using State = TreeAutomata::State;
//     using StateSet = TreeAutomata::StateSet;
//     using StateScaleSet = std::set<std::pair<State, std::pair<AUTOQ::Complex::Complex, AUTOQ::Complex::Complex>>, PairComparator>;
//     StateSet As_finalStates(Q.finalStates.begin(), Q.finalStates.end());
//     std::map<State, std::set<StateScaleSet>> processed; // Line 1: ← ∅;
//     std::map<State, std::set<StateScaleSet>> worklist;

//     TreeAutomata::BottomUpTransitions R_transitions;
//     for (const auto &t : this->transitions) {
//         const auto &symbol_tag = t.first;
//         for (const auto &out_ins : t.second) {
//             auto s = out_ins.first;
//             for (const auto &in : out_ins.second)
//                 R_transitions[symbol_tag][in].insert(s);
//         }
//     }
//     TreeAutomata::BottomUpTransitions Q_transitions;
//     for (const auto &t : Q.transitions) {
//         const auto &symbol_tag = t.first;
//         for (const auto &out_ins : t.second) {
//             auto s = out_ins.first;
//             for (const auto &in : out_ins.second)
//                 Q_transitions[symbol_tag][in].insert(s);
//         }
//     }

//     /************************************/
//     // Line 2-4: Construct the initial worklist!
//     for (const auto &tr : R_transitions) {
//         if (tr.first.is_leaf()) {
//             const auto &vr = tr.first;
//             const auto &cr = vr.symbol().complex;
//             for (const auto &sr : tr.second.at({})) {
//                 StateScaleSet Uq;
//                 if (cr.isZero()) {
//                     for (const auto &tq : Q_transitions) {
//                         if (tq.first.is_leaf()) {
//                             const auto &vq = tq.first;
//                             const auto &cq = vq.symbol().complex;
//                             if (cq.isZero()) {
//                                 for (const auto &uq : tq.second.at({})) {
//                                     Uq.insert({uq, {cr, cq}}); // here 0 := ?
//                                 }
//                             }
//                         }
//                     }
//                 } else { // cr is not zero
//                     for (const auto &tq : Q_transitions) {
//                         if (tq.first.is_leaf()) {
//                             const auto &vq = tq.first;
//                             const auto &cq = vq.symbol().complex;
//                             if (!cq.isZero()) {
//                                 for (const auto &uq : tq.second.at({})) {
//                                     Uq.insert({uq, {cq, cr}});
//                                 }
//                             }
//                         }
//                     }
//                 }
//                 #ifdef MIN
//                 auto copy = worklist[sr]; // Min{...}
//                 for (const auto &t : copy) {
//                     if (std::includes(t.begin(), t.end(), Uq.begin(), Uq.end()))
//                         worklist[sr].erase(t);
//                 }
//                 bool cancel = false;
//                 for (const auto &t : worklist[sr]) {
//                     if (std::includes(Uq.begin(), Uq.end(), t.begin(), t.end())) {
//                         cancel = true;
//                         break;
//                     }
//                 }
//                 if (!cancel)
//                 #endif
//                     worklist[sr].insert(Uq);
//             }
//         }
//     }
//     /************************************/
//     while (!worklist.empty()) { // Line 5
//         /*********************************************/
//         // Line 6
//         auto it = worklist.begin(); // const auto &it ?
//         if (it->second.empty()) {
//             worklist.erase(it);
//             continue;
//         }
//         auto sr = it->first;
//         auto Uq = *(it->second.begin());
//         it->second.erase(it->second.begin());
//         /*********************************************/
//         // Line 7
//         if (this->finalStates.contains(sr)) {
//             StateSet ss;
//             for (const auto &uq_c : Uq) {
//                 auto uq = uq_c.first;
//                 ss.insert(uq);
//             }
//             std::set<int> intersection; // Create a set to store the intersection
//             std::set_intersection( // Use set_intersection to find the common elements
//                 ss.begin(), ss.end(),
//                 Q.finalStates.begin(), Q.finalStates.end(),
//                 std::inserter(intersection, intersection.begin())
//             );
//             if (intersection.empty()) { // Check if the intersection is empty
//                 return false;
//             }
//         }
//         /*********************************************/
//         // Line 8
//         #ifdef MIN
//         auto copy = processed[sr]; // Min{...}
//         for (const auto &t : copy) {
//             if (std::includes(t.begin(), t.end(), Uq.begin(), Uq.end()))
//                 processed[sr].erase(t);
//         }
//         bool cancel = false;
//         for (const auto &t : processed[sr]) {
//             if (std::includes(Uq.begin(), Uq.end(), t.begin(), t.end())) {
//                 cancel = true;
//                 break;
//             }
//         }
//         if (!cancel)
//         #endif
//             processed[sr].insert(Uq);
//         // std::cout << AUTOQ::Util::Convert::ToString(processed) << "\n";
//         /*********************************************/
//         // Line 10
//         auto sr1 = sr;
//         const auto &Uq1 = Uq;
//         for (const auto &kv : processed) {
//             auto sr2 = kv.first;
//             for (const auto &Uq2 : kv.second) {
//                 for (const auto &tr : R_transitions) {
//                     const auto &alpha = tr.first;
//                     /*********************************************/
//                     // Line 11
//                     auto Hr_ptr = tr.second.find({sr1, sr2});
//                     if (Hr_ptr == tr.second.end()) continue;
//                     StateSet Hr = Hr_ptr->second;
//                     if (Hr.empty()) continue;
//                     /*********************************************/
//                     StateScaleSet Uq_; // Line 12
//                     /*********************************************/
//                     // Line 13
//                     for (const auto &kv1 : Uq1) {
//                         const auto &sq1 = kv1.first;
//                         const auto &r1 = kv1.second;
//                         for (const auto &kv2 : Uq2) {
//                             const auto &sq2 = kv2.first;
//                             const auto &r2 = kv2.second;
//                             /*********************************************/
//                             // Line 15
//                             StateSet sqSet;
//                             auto it = Q_transitions.find(alpha);
//                             if (it != Q_transitions.end()) {
//                                 auto ptr = it->second.find({sq1, sq2});
//                                 if (ptr == it->second.end()) continue;
//                                 sqSet = ptr->second;
//                             }
//                             if (sqSet.empty()) continue;
//                             // Line 14
//                             if (!(r1.first * r2.second).valueEqual(r1.second * r2.first) && !r1.first.isZero() && !r2.first.isZero()) {
//                                 continue;
//                             }
//                             /*********************************************/
//                             // Line 16
//                             auto c = r1.first.isZero() ? r2 : r1;
//                             for (const auto &sq : sqSet) {
//                                 Uq_.insert(std::make_pair(sq, c));
//                             }
//                             /*********************************************/
//                         }
//                     }
//                     /*********************************************/
//                     // Line 17-18
//                     for (const auto &sr_ : Hr) {
//                         if (!processed[sr_].contains(Uq_) && !worklist[sr_].contains(Uq_)) {
//                             #ifdef MIN
//                             auto copy = worklist[sr_]; // Min{...}
//                             for (const auto &t : copy) {
//                                 if (std::includes(t.begin(), t.end(), Uq_.begin(), Uq_.end()))
//                                     worklist[sr_].erase(t);
//                             }
//                             bool cancel = false;
//                             for (const auto &t : worklist[sr_]) {
//                                 if (std::includes(Uq_.begin(), Uq_.end(), t.begin(), t.end())) {
//                                     cancel = true;
//                                     break;
//                                 }
//                             }
//                             if (!cancel)
//                             #endif
//                                 worklist[sr_].insert(Uq_);
//                         }
//                     }
//                     /*********************************************/
//                 }
//             }
//         }
//         auto sr2 = sr;
//         const auto &Uq2 = Uq;
//         for (const auto &kv : processed) {
//             auto sr1 = kv.first;
//             for (const auto &Uq1 : kv.second) {
//                 if (sr1 == sr2 && Uq1 == Uq2) continue;
//                 for (const auto &tr : R_transitions) {
//                     const auto &alpha = tr.first;
//                     /*********************************************/
//                     // Line 11
//                     auto Hr_ptr = tr.second.find({sr1, sr2});
//                     if (Hr_ptr == tr.second.end()) continue;
//                     StateSet Hr = Hr_ptr->second;
//                     if (Hr.empty()) continue;
//                     /*********************************************/
//                     StateScaleSet Uq_; // Line 12
//                     /*********************************************/
//                     // Line 13
//                     for (const auto &kv1 : Uq1) {
//                         const auto &sq1 = kv1.first;
//                         const auto &r1 = kv1.second;
//                         for (const auto &kv2 : Uq2) {
//                             const auto &sq2 = kv2.first;
//                             const auto &r2 = kv2.second;
//                             /*********************************************/
//                             // Line 15
//                             StateSet sqSet;
//                             auto it = Q_transitions.find(alpha);
//                             if (it != Q_transitions.end()) {
//                                 auto ptr = it->second.find({sq1, sq2});
//                                 if (ptr == it->second.end()) continue;
//                                 sqSet = ptr->second;
//                             }
//                             if (sqSet.empty()) continue;
//                             // Line 14
//                             if (!(r1.first * r2.second).valueEqual(r1.second * r2.first) && !r1.first.isZero() && !r2.first.isZero()) {
//                                 continue;
//                             }
//                             /*********************************************/
//                             // Line 16
//                             auto c = r1.first.isZero() ? r2 : r1;
//                             for (const auto &sq : sqSet) {
//                                 Uq_.insert(std::make_pair(sq, c));
//                             }
//                             /*********************************************/
//                         }
//                     }
//                     /*********************************************/
//                     // Line 17-18
//                     for (const auto &sr_ : Hr) {
//                         if (!processed[sr_].contains(Uq_) && !worklist[sr_].contains(Uq_)) {
//                             #ifdef MIN
//                             auto copy = worklist[sr_]; // Min{...}
//                             for (const auto &t : copy) {
//                                 if (std::includes(t.begin(), t.end(), Uq_.begin(), Uq_.end()))
//                                     worklist[sr_].erase(t);
//                             }
//                             bool cancel = false;
//                             for (const auto &t : worklist[sr_]) {
//                                 if (std::includes(Uq_.begin(), Uq_.end(), t.begin(), t.end())) {
//                                     cancel = true;
//                                     break;
//                                 }
//                             }
//                             if (!cancel)
//                             #endif
//                                 worklist[sr_].insert(Uq_);
//                         }
//                     }
//                     /*********************************************/
//                 }
//             }
//         }
//     }
//     return true;
// }
// template <>
// bool AUTOQ::SymbolicAutomata::operator<<=(SymbolicAutomata Q) const {
//     SymbolicAutomata R = *this;
//     Q = Q.operator||(AUTOQ::SymbolicAutomata::zero_amplitude(Q.qubitNum));
//     R.k_unification(); Q.k_unification();
//     // R.print("R:\n"); Q.print("Q:\n");

//     // if (R.StrictlyEqual(Q)) return true;
//     auto start = std::chrono::steady_clock::now();

//     using State = SymbolicAutomata::State;
//     using StateSet = SymbolicAutomata::StateSet;
//     using SymbolicComplex = AUTOQ::Complex::SymbolicComplex;
//     using StateScaleSet = std::set<std::pair<State, unsigned>>; // int <-> std::pair<SymbolicComplex, SymbolicComplex>
//     StateSet As_finalStates(Q.finalStates.begin(), Q.finalStates.end());
//     std::map<State, std::set<StateScaleSet>> processed; // Line 1: ← ∅;
//     std::map<State, std::set<StateScaleSet>> worklist;

//     /*********************************************************/
//     // Rename the variables in R's transitions and constraints!
//     auto transitions2 = R.transitions;
//     for (const auto &tr : transitions2) {
//         if (tr.first.symbol().is_leaf()) {
//             AUTOQ::Complex::SymbolicComplex complex_new;
//             for (const auto &t_c : tr.first.symbol().complex) { // Term -> Complex
//                 auto term = t_c.first;
//                 AUTOQ::Complex::Term term2;
//                 for (const auto &v_i : term) { // std::string -> boost::multiprecision::cpp_int
//                     if (R.vars.contains(v_i.first))
//                         term2[v_i.first + "_R"] = v_i.second;
//                     else
//                         term2[v_i.first] = v_i.second;
//                 }
//                 complex_new[term2] = t_c.second;
//             }
//             R.transitions.erase(tr.first.symbol());
//             R.transitions[AUTOQ::Symbol::Symbolic(complex_new)] = tr.second;
//         }
//     }
//     for (const auto &var : R.vars)
//         R.constraints = std::regex_replace(R.constraints, std::regex("(\\b" + var + "\\b)"), var + "_R");
//     if (AUTOQ::String::trim(R.constraints).empty()) R.constraints = "true";
//     /*********************************************************/
//     // Rename the variables in Q's transitions and constraints!
//     transitions2 = Q.transitions;
//     for (const auto &tr : transitions2) {
//         if (tr.first.symbol().is_leaf()) {
//             AUTOQ::Complex::SymbolicComplex complex_new;
//             for (const auto &t_c : tr.first.symbol().complex) { // Term -> Complex
//                 auto term = t_c.first;
//                 AUTOQ::Complex::Term term2;
//                 for (const auto &v_i : term) { // std::string -> boost::multiprecision::cpp_int
//                     if (Q.vars.contains(v_i.first))
//                         term2[v_i.first + "_Q"] = v_i.second;
//                     else
//                         term2[v_i.first] = v_i.second;
//                 }
//                 complex_new[term2] = t_c.second;
//             }
//             Q.transitions.erase(tr.first.symbol());
//             Q.transitions[AUTOQ::Symbol::Symbolic(complex_new)] = tr.second;
//         }
//     }
//     for (const auto &var : Q.vars)
//         Q.constraints = std::regex_replace(Q.constraints, std::regex("(\\b" + var + "\\b)"), var + "_Q");
//     if (AUTOQ::String::trim(Q.constraints).empty()) Q.constraints = "true";
//     /*********************************************************/
//     std::string all_var_definitions;
//     for (const auto &var : R.vars)
//         all_var_definitions += "(declare-fun " + var + "_R () Real)";
//     for (const auto &var : Q.vars)
//         all_var_definitions += "(declare-fun " + var + "_Q () Real)";

//     SymbolicAutomata::BottomUpTransitions R_transitions;
//     for (const auto &t : R.transitions) {
//         const auto &symbol_tag = t.first;
//         for (const auto &out_ins : t.second) {
//             auto s = out_ins.first;
//             for (const auto &in : out_ins.second)
//                 R_transitions[symbol_tag][in].insert(s);
//         }
//     }
//     SymbolicAutomata::BottomUpTransitions Q_transitions;
//     for (const auto &t : Q.transitions) {
//         const auto &symbol_tag = t.first;
//         for (const auto &out_ins : t.second) {
//             auto s = out_ins.first;
//             for (const auto &in : out_ins.second)
//                 Q_transitions[symbol_tag][in].insert(s);
//         }
//     }


//     /************************************/
//     // Line 2-3: Construct the initial worklist!
//     std::map<std::pair<SymbolicComplex, SymbolicComplex>, int> ratioInverseMap;
//     std::vector<std::pair<SymbolicComplex, SymbolicComplex>> ratioMap;
//     for (const auto &tr : R_transitions) {
//         if (tr.first.is_leaf()) {
//             const auto &vr = tr.first;
//             const auto &cr = vr.symbol().complex;
//             for (const auto &sr : tr.second.at({})) {
//                 StateScaleSet Uq;
//                 for (const auto &tq : Q_transitions) {
//                     if (tq.first.is_leaf()) {
//                         const auto &vq = tq.first;
//                         const auto &cq = vq.symbol().complex;
//                         // std::cout << cq.realToSMT() << "\n";
//                         // std::cout << cq.imagToSMT() << "\n";
//                         // std::cout << cr.realToSMT() << "\n";
//                         // std::cout << cr.imagToSMT() << "\n";
//                         if (call_smt_solver(all_var_definitions, // existential filter for efficiency
//                                 "(or (and (= " + cq.realToSMT() + " 0)(= " + cq.imagToSMT() + " 0)(= " + cr.realToSMT() + " 0)(= " + cr.imagToSMT() + " 0))" // cq == 0 && cr == 0
//                                  + " (and (or (not (= " + cq.realToSMT() + " 0))(not (= " + cq.imagToSMT() + " 0)))(or (not (= " + cr.realToSMT() + " 0))(not (= " + cr.imagToSMT() + " 0)))))") // cq != 0 && cr != 0
//                         ) {
//                             for (const auto &uq : tq.second.at({})) {
//                                 auto it = ratioInverseMap.find({cq, cr});
//                                 if (it == ratioInverseMap.end()) {
//                                     ratioInverseMap[{cq, cr}] = ratioInverseMap.size();
//                                     it = ratioInverseMap.find({cq, cr});
//                                     ratioMap.push_back({cq, cr});
//                                 }
//                                 Uq.insert({uq, 1 << (it->second)});
//                             }
//                         }
//                     }
//                 }
//                 #ifdef MIN
//                 auto copy = worklist[sr]; // Min{...}
//                 for (const auto &t : copy) {
//                     if (std::includes(t.begin(), t.end(), Uq.begin(), Uq.end()))
//                         worklist[sr].erase(t);
//                 }
//                 bool cancel = false;
//                 for (const auto &t : worklist[sr]) {
//                     if (std::includes(Uq.begin(), Uq.end(), t.begin(), t.end())) {
//                         cancel = true;
//                         break;
//                     }
//                 }
//                 if (!cancel)
//                 #endif
//                     worklist[sr].insert(Uq);
//             }
//         }
//     }
//     // std::cout << "Worklist: " << AUTOQ::Util::Convert::ToString(worklist) << "\n";
//     /************************************/
//     // std::cout << AUTOQ::Util::Convert::ToString(ratioMap) << std::endl;
//     // std::cout << AUTOQ::Util::Convert::ToString(ratioInverseMap) << std::endl;

//     /************************************/
//     while (!worklist.empty()) { // Line 4
//         /*********************************************/
//         // Line 5
//         auto it = worklist.begin(); // const auto &it ?
//         if (it->second.empty()) {
//             worklist.erase(it);
//             continue;
//         }
//         auto sr = it->first;
//         auto Uq = *(it->second.begin());
//         it->second.erase(it->second.begin());
//         /*********************************************/
//         // Line 6
//         if (R.finalStates.contains(sr)) {
//             std::set<unsigned> formulas; // set of formulas
//             for (const auto &uq_c : Uq) {
//                 auto uq = uq_c.first;
//                 if (Q.finalStates.contains(uq))
//                     formulas.insert(uq_c.second);
//             }
//             if (formulas.empty()) { // Check if the intersection is empty
//                 auto duration = std::chrono::steady_clock::now() - start;
//                 // std::cout << AUTOQ::Util::print_duration(duration) << "\n";
//                 // R.print_language("R:\n");
//                 // Q.print_language("Q:\n");
//                 return false;
//             }
//             std::string assertion = "(not (or";
//             for (const auto &formula : formulas) {
//                 auto x = formula;
//                 std::vector<int> current;
//                 for (int i = 0; x > 0; ++i) {
//                     if (x & 1) {
//                         current.push_back(i);
//                     }
//                     x >>= 1;
//                 }
//                 assert(!current.empty());
//                 std::string ratio_constraint = "(and";
//                 for (unsigned i=1; i<current.size(); ++i) {
//                     const auto &c1u = ratioMap[current[i-1]].first;
//                     const auto &c1d = ratioMap[current[i-1]].second;
//                     const auto &c2u = ratioMap[current[i]].first;
//                     const auto &c2d = ratioMap[current[i]].second;
//                     ratio_constraint += " (= " + (c1u * c2d).realToSMT() + " " + (c1d * c2u).realToSMT() + ")";
//                     ratio_constraint += " (= " + (c1u * c2d).imagToSMT() + " " + (c1d * c2u).imagToSMT() + ")";
//                 }
//                 for (unsigned i=0; i<current.size(); ++i) {
//                     const auto &cu = ratioMap[current[i]].first;
//                     const auto &cd = ratioMap[current[i]].second;
//                     ratio_constraint += "(or (and (= " + cu.realToSMT() + " 0)(= " + cu.imagToSMT() + " 0)(= " + cd.realToSMT() + " 0)(= " + cd.imagToSMT() + " 0))" // cu == 0 && cd == 0
//                         + " (and (or (not (= " + cu.realToSMT() + " 0))(not (= " + cu.imagToSMT() + " 0)))(or (not (= " + cd.realToSMT() + " 0))(not (= " + cd.imagToSMT() + " 0)))))"; // cu != 0 && cd != 0
//                 }
//                 ratio_constraint += ")"; // 𝜓
//                 std::string implies_constraint = "(or (not " + R.constraints + ") (and " + Q.constraints + " " + ratio_constraint + "))"; // 𝜑𝑟 ⇒ (𝜑𝑞 ∧ 𝜓)
//                 std::string formula_constraint;
//                 if (!Q.vars.empty()) {
//                     formula_constraint = "(exists (";
//                     for (const auto &var : Q.vars) // (forall ((x1 σ1) (x2 σ2) ··· (xn σn)) (exists ((x1 σ1) (x2 σ2) ··· (xn σn)) ϕ))
//                         formula_constraint += "(" + var + "_Q Real)";
//                     formula_constraint += ") ";
//                     formula_constraint += implies_constraint;
//                     formula_constraint += ")";
//                 } else {
//                     formula_constraint = implies_constraint;
//                 }
//                 assertion += " " + formula_constraint;
//             }
//             assertion += "))";
//             std::string define_varR;
//             for (const auto &var : R.vars)
//                 define_varR += "(declare-fun " + var + "_R () Real)";
//             if (call_smt_solver(define_varR, assertion)) {
//                 auto duration = std::chrono::steady_clock::now() - start;
//                 // std::cout << AUTOQ::Util::print_duration(duration) << "\n";
//                 // R.print_language("R:\n");
//                 // Q.print_language("Q:\n");
//                 return false;
//             }
//         }
//         /*********************************************/
//         // Line 7
//         #ifdef MIN
//         auto copy = processed[sr]; // Min{...}
//         for (const auto &t : copy) {
//             if (std::includes(t.begin(), t.end(), Uq.begin(), Uq.end()))
//                 processed[sr].erase(t);
//         }
//         bool cancel = false;
//         for (const auto &t : processed[sr]) {
//             if (std::includes(Uq.begin(), Uq.end(), t.begin(), t.end())) {
//                 cancel = true;
//                 break;
//             }
//         }
//         if (!cancel)
//         #endif
//             processed[sr].insert(Uq);
//         // std::cout << AUTOQ::Util::Convert::ToString(processed) << "\n";
//         /*********************************************/
//         // Line 8-9
//         auto sr1 = sr;
//         const auto &Uq1 = Uq;
//         for (const auto &kv : processed) {
//             auto sr2 = kv.first;
//             for (const auto &Uq2 : kv.second) {
//                 for (const auto &tr : R_transitions) {
//                     const auto &alpha = tr.first;
//                     /*********************************************/
//                     // Line 10
//                     auto Hr_ptr = tr.second.find({sr1, sr2});
//                     if (Hr_ptr == tr.second.end()) continue;
//                     StateSet Hr = Hr_ptr->second;
//                     if (Hr.empty()) continue;
//                     /*********************************************/
//                     StateScaleSet Uq_; // Line 11
//                     /*********************************************/
//                     // Line 12-13
//                     for (const auto &kv1 : Uq1) {
//                         const auto &sq1 = kv1.first;
//                         const auto &c1_set = kv1.second;
//                         assert(c1_set > 0);
//                         for (const auto &kv2 : Uq2) {
//                             const auto &sq2 = kv2.first;
//                             const auto &c2_set = kv2.second;
//                             assert(c2_set > 0);
//                             /*********************************************/
//                             // Line 13
//                             StateSet sqSet;
//                             auto it = Q_transitions.find(alpha);
//                             if (it != Q_transitions.end()) {
//                                 auto ptr = it->second.find({sq1, sq2});
//                                 if (ptr == it->second.end()) continue;
//                                 sqSet = ptr->second;
//                             }
//                             if (sqSet.empty()) continue;
//                             // Line 13
//                             unsigned unionSet = c1_set | c2_set;
//                             for (const auto &sq : sqSet) {
//                                 Uq_.insert(std::make_pair(sq, unionSet));
//                             }
//                             /*********************************************/
//                         }
//                     }
//                     /*********************************************/
//                     // Line 14-17
//                     for (const auto &sr_ : Hr) {
//                         if (!processed[sr_].contains(Uq_) && !worklist[sr_].contains(Uq_)) {
//                             #ifdef MIN
//                             auto copy = worklist[sr_]; // Min{...}
//                             for (const auto &t : copy) {
//                                 if (std::includes(t.begin(), t.end(), Uq_.begin(), Uq_.end()))
//                                     worklist[sr_].erase(t);
//                             }
//                             bool cancel = false;
//                             for (const auto &t : worklist[sr_]) {
//                                 if (std::includes(Uq_.begin(), Uq_.end(), t.begin(), t.end())) {
//                                     cancel = true;
//                                     break;
//                                 }
//                             }
//                             if (!cancel)
//                             #endif
//                                 worklist[sr_].insert(Uq_);
//                             // std::cout << AUTOQ::Util::Convert::ToString(worklist) << "\n";
//                         }
//                     }
//                     /*********************************************/
//                 }
//             }
//         }
//         auto sr2 = sr;
//         const auto &Uq2 = Uq;
//         for (const auto &kv : processed) {
//             auto sr1 = kv.first;
//             for (const auto &Uq1 : kv.second) {
//                 if (sr1 == sr2 && Uq1 == Uq2) continue;
//                 for (const auto &tr : R_transitions) {
//                     const auto &alpha = tr.first;
//                     /*********************************************/
//                     // Line 10
//                     auto Hr_ptr = tr.second.find({sr1, sr2});
//                     if (Hr_ptr == tr.second.end()) continue;
//                     StateSet Hr = Hr_ptr->second;
//                     if (Hr.empty()) continue;
//                     /*********************************************/
//                     StateScaleSet Uq_; // Line 11
//                     /*********************************************/
//                     // Line 12-13
//                     for (const auto &kv1 : Uq1) {
//                         const auto &sq1 = kv1.first;
//                         const auto &c1_set = kv1.second;
//                         assert(c1_set > 0);
//                         for (const auto &kv2 : Uq2) {
//                             const auto &sq2 = kv2.first;
//                             const auto &c2_set = kv2.second;
//                             assert(c2_set > 0);
//                             /*********************************************/
//                             // Line 13
//                             StateSet sqSet;
//                             auto it = Q_transitions.find(alpha);
//                             if (it != Q_transitions.end()) {
//                                 auto ptr = it->second.find({sq1, sq2});
//                                 if (ptr == it->second.end()) continue;
//                                 sqSet = ptr->second;
//                             }
//                             if (sqSet.empty()) continue;
//                             // Line 13
//                             unsigned unionSet = c1_set | c2_set;
//                             for (const auto &sq : sqSet) {
//                                 Uq_.insert(std::make_pair(sq, unionSet));
//                             }
//                             /*********************************************/
//                         }
//                     }
//                     /*********************************************/
//                     // Line 14-17
//                     for (const auto &sr_ : Hr) {
//                         if (!processed[sr_].contains(Uq_) && !worklist[sr_].contains(Uq_)) {
//                             #ifdef MIN
//                             auto copy = worklist[sr_]; // Min{...}
//                             for (const auto &t : copy) {
//                                 if (std::includes(t.begin(), t.end(), Uq_.begin(), Uq_.end()))
//                                     worklist[sr_].erase(t);
//                             }
//                             bool cancel = false;
//                             for (const auto &t : worklist[sr_]) {
//                                 if (std::includes(Uq_.begin(), Uq_.end(), t.begin(), t.end())) {
//                                     cancel = true;
//                                     break;
//                                 }
//                             }
//                             if (!cancel)
//                             #endif
//                                 worklist[sr_].insert(Uq_);
//                             // std::cout << AUTOQ::Util::Convert::ToString(worklist) << "\n";
//                         }
//                     }
//                     /*********************************************/
//                 }
//             }
//         }
//     }
//     auto duration = std::chrono::steady_clock::now() - start;
//     // std::cout << AUTOQ::Util::print_duration(duration) << "\n";
//     return true;
// }