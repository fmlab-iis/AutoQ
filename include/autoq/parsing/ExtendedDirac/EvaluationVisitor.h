
#include "ExtendedDiracParserBaseVisitor.h"
#include "ExtendedDiracParser.h"

#include "autoq/aut_description.hh"
#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/complex/complex.hh"
#include "autoq/complex/constrained_complex.hh"

#include <queue>

AUTOQ::Automata<AUTOQ::Symbol::Constrained> efficiently_construct_singleton_lsta(const std::map<std::string, AUTOQ::Complex::ConstrainedComplex> &ket2amp) {
    using State = AUTOQ::Automata<AUTOQ::Symbol::Constrained>::State;

    AUTOQ::Automata<AUTOQ::Symbol::Constrained> aut;
    AUTOQ::Complex::ConstrainedComplex default_amp;

    // Step 1. Build the array map from kets to LSTA states at each level.
    std::map<std::string, State> ket2st;
    for (const auto &[ket, amp] : ket2amp) {
        ket2st[ket] = 0;
    }
    // IMPORTANT NOTE: We assume ket2amp[ket] are initialized to 0 automatically.
    // Also remember to specify the number of qubits!
    // if (aut.qubitNum == 0) {
        aut.qubitNum = ket2amp.begin()->first.length();
    // } else if (aut.qubitNum != static_cast<int>(ket.length())) {
    //     THROW_AUTOQ_ERROR("The numbers of qubits in different |...⟩'s are not consistent!");
    // }
    aut.finalStates.push_back(0);
    aut.stateNum = 1; // since we already have 0 for the root state

    // Step 2. We start to construct the automaton below level by level.
    std::optional<State> default_state; // no values by default
    for (int level=1; level<=aut.qubitNum; level++) {
        // transitions to be constructed at this level
        std::map<std::pair<State, bool>, std::pair<std::optional<State>, std::optional<State>>> newTrans; // (top, var?) -> (left, right)
        // Notice that only one of newTrans[{st, false}] and newTrans[{st, true}] can exist, but it is inherently guaranteed by the logic.

        // Step 2-a. Build newTrans with known states so far and update the new children into ket2st.
        bool hasVar = false;
        for (auto &[ket, st] : ket2st) {
            char dir = ket.at(level-1); // -1 because the index starts from 0
            std::optional<State> &newState = [&]() -> std::optional<State>& {
                if (dir == '0') {
                    return newTrans[std::make_pair(st, false)].first;
                } else if (dir == '1') {
                    return newTrans[std::make_pair(st, false)].second;
                } else if (dir == 'L') { // loop variable: i
                    hasVar = true;
                    return newTrans[std::make_pair(st, true)].first;
                } else if (dir == 'R') { // loop variable: i'
                    hasVar = true;
                    return newTrans[std::make_pair(st, true)].second;
                } else {
                    THROW_AUTOQ_ERROR("This is an unhandled case!");
                }
            }();
            // Note that "st" is a reference here.
            if (newState.has_value()) {
                st = newState.value();
            } else {
                st = aut.stateNum++;
                newState = st;
            }
        }

        // Step 2-b. Check if a default state is needed at this level.
        // If the default state at the previous level already exists, also create another one at this level.
        // Otherwise, create if needed during the traversal of newTrans.
        if (default_state.has_value()) {
            auto old = default_state.value();
            default_state = aut.stateNum++;
            if (hasVar)
                aut.transitions[typename AUTOQ::Automata<AUTOQ::Symbol::Constrained>::SymbolTag(AUTOQ::Symbol::Constrained(level), typename AUTOQ::Automata<AUTOQ::Symbol::Constrained>::Tag(2 | 1))][old].insert({default_state.value(), default_state.value()});
            else
                aut.transitions[typename AUTOQ::Automata<AUTOQ::Symbol::Constrained>::SymbolTag(AUTOQ::Symbol::Constrained(level), typename AUTOQ::Automata<AUTOQ::Symbol::Constrained>::Tag(1))][old].insert({default_state.value(), default_state.value()});
        }
        // Now "default_state" has been updated (if it is extended from the previous level)!

        // Step 2-c. Construct the transitions from newTrans at this level.
        for (auto &[top_isVar, children] : newTrans) {
            auto &left = children.first;
            auto &right = children.second;
            if (!left.has_value()) {
                if (!default_state.has_value()) {
                    default_state = aut.stateNum++;
                }
                left = default_state;
            }
            if (!right.has_value()) {
                if (!default_state.has_value()) {
                    default_state = aut.stateNum++;
                }
                right = default_state;
            }
            auto top = top_isVar.first;
            auto isVar = top_isVar.second;
            if (isVar) {
                aut.transitions[typename AUTOQ::Automata<AUTOQ::Symbol::Constrained>::SymbolTag(AUTOQ::Symbol::Constrained(level), typename AUTOQ::Automata<AUTOQ::Symbol::Constrained>::Tag(1))][top].insert({left.value(), right.value()});
                aut.transitions[typename AUTOQ::Automata<AUTOQ::Symbol::Constrained>::SymbolTag(AUTOQ::Symbol::Constrained(level), typename AUTOQ::Automata<AUTOQ::Symbol::Constrained>::Tag(2))][top].insert({right.value(), left.value()});
            } else {
                aut.transitions[typename AUTOQ::Automata<AUTOQ::Symbol::Constrained>::SymbolTag(AUTOQ::Symbol::Constrained(level), typename AUTOQ::Automata<AUTOQ::Symbol::Constrained>::Tag(1))][top].insert({left.value(), right.value()});
            }
        }
    }
    // Step 2-d. Finally, create leaf transitions.
    for (const auto &[ket, st] : ket2st) {
        auto amp = ket2amp.at(ket);
        aut.transitions[typename AUTOQ::Automata<AUTOQ::Symbol::Constrained>::SymbolTag(AUTOQ::Symbol::Constrained(amp), typename AUTOQ::Automata<AUTOQ::Symbol::Constrained>::Tag(1))][st].insert({{}});
    } // Also don't forget the default value!!!
    if (default_state.has_value())
        aut.transitions[typename AUTOQ::Automata<AUTOQ::Symbol::Constrained>::SymbolTag(AUTOQ::Symbol::Constrained(default_amp), typename AUTOQ::Automata<AUTOQ::Symbol::Constrained>::Tag(1))][default_state.value()].insert({{}});
    aut.reduce();
    return aut;
}

class CustomErrorListener : public antlr4::BaseErrorListener {
public:
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wunused-parameter"
    void syntaxError(antlr4::Recognizer *recognizer,
                     antlr4::Token *offendingSymbol,
                     size_t line, size_t charPositionInLine,
                     const std::string &msg,
                     std::exception_ptr e) override {
        THROW_AUTOQ_ERROR("Parsing Error: Line " + std::to_string(line) + ":" + std::to_string(charPositionInLine)
              + " in ExtendedDirac.g4 - " + msg);
    }
    #pragma GCC diagnostic pop
};

template <typename Symbol, typename Symbol2 = Symbol>
struct EvaluationVisitor : public ExtendedDiracParserBaseVisitor {
    typedef std::pair<int, int> unitsplit_t;
    typedef std::vector<unitsplit_t> strsplit_t;
    typedef std::vector<strsplit_t> strs2split_t;
    typedef std::vector<strs2split_t> segment2strs_t;
    typedef std::vector<std::vector<unitsplit_t>> segment2split_t;
    typedef std::vector<unitsplit_t> currentSplit_t;
    typedef std::pair<int, int> edge_t; // unordered: using std::minmax
    typedef std::set<edge_t> graph_t;
    typedef std::vector<int> cc_t;
    typedef std::set<cc_t> perm_t;
    typedef std::vector<perm_t> segment2perm_t;
    typedef std::pair<char, std::string> eq_t;
    typedef std::map<char, std::string> eqs_t;
    typedef std::pair<std::string, std::string> ineq_t; // unordered: using std::minmax, notice that we do not use char here because there may be some binary strings as constants in future use.
    typedef std::set<ineq_t> ineqS_t;
    typedef std::set<char> vars_t;
    typedef std::vector<vars_t> unit2vars_t;
    typedef std::pair<unit2vars_t, ineqS_t> relation_t;
    typedef std::pair<std::set<char>, std::string> varcon_t; // ordered
    typedef std::vector<varcon_t> varconS_t;

    enum mode_t {EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT,
                 SPLIT_TENSORED_EXPRESSION_INTO_VECTOR_OF_SETS_WITHOUT_TENSOR, // new!!!
                 COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES, // may input with ;
                 REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT, // may input with ;
                 COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION, // may input with ;
                 REORDER_UNITS_BY_THE_GROUP, // may input with ;
                 EVALUATE_EACH_SET_BRACES_TO_LSTA,
                 SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS, // a submode in EVALUATE_EACH_SET_BRACES_TO_LSTA
                 SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY // a submode in EVALUATE_EACH_SET_BRACES_TO_LSTA
                };
    mode_t mode; // by default, the first one

    std::map<char, int> globalVar2len; // record all control variables used in {diracs : varcons}
    std::set<char> usedVars; // record all variables currently used in {diracs : varcons} for preventing naming collision.
    segment2split_t segment2split;
    currentSplit_t currentSplit;
    segment2perm_t segment2perm;
    perm_t currentPerm;
    std::vector<size_t> remember_the_lengths_of_each_unit_position;
    bool switch_symbol_to_second;
    bool do_not_throw_term_undefined_error;
    bool encountered_term_undefined_error;

    std::map<std::string, AUTOQ::Complex::Complex> constants, constants2;
    std::map<std::string, std::string> predicates, predicates2;
    EvaluationVisitor(const std::map<std::string, AUTOQ::Complex::Complex> &constants, const std::map<std::string, std::string> &predicates) :
        mode(EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT),
        globalVar2len(),
        usedVars(),
        segment2split(),
        currentSplit(),
        segment2perm(),
        currentPerm(),
        remember_the_lengths_of_each_unit_position(),
        switch_symbol_to_second(false),
        do_not_throw_term_undefined_error(false),
        encountered_term_undefined_error(false),
        constants(constants),
        constants2(),
        predicates(predicates),
        predicates2() {}
    std::any let_visitor_parse_string(const std::string &input) {
        antlr4::ANTLRInputStream inputStream(input);
        ExtendedDiracLexer lexer(&inputStream);
        antlr4::CommonTokenStream tokens(&lexer);
        ExtendedDiracParser parser(&tokens);
        parser.removeErrorListeners(); // Remove the default error listener
        CustomErrorListener errorListener;
        parser.addErrorListener(&errorListener); // Add a custom error listener
        ExtendedDiracParser::ExprContext* tree = parser.expr(); // Parse the input
        return this->visit(tree);
    }

    // std::any visitExtendedDirac(ExtendedDiracParser::ExtendedDiracContext *ctx) override {
    //     if (ctx->muloperators() != nullptr) { // RULE: accepted WHERE NEWLINES muloperators
    //         visit(ctx->muloperators()); // Notice that "mulmap" will be updated during the visit.
    //     }
    //     auto result = visit(ctx->accepted()); // RULE: accepted (WHERE NEWLINES muloperators)?
    //     if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Concrete>) {
    //         AUTOQ::Symbol::Concrete::mulmap.clear();
    //     } else if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Predicate>) {
    //         AUTOQ::Symbol::Predicate::mulmap.clear();
    //     } else { // if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Symbolic>) {
    //         // do nothing
    //     }
    //     return result;
    // }

    // std::any visitMuloperators(ExtendedDiracParser::MuloperatorsContext *ctx) override {
    //     for (const auto &e : ctx->muloperator()) {
    //         visit(e); // RULE: muloperator+
    //     }
    //     return {};
    // }

    // std::any visitMuloperator(ExtendedDiracParser::MuloperatorContext *ctx) override {
    //     if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Concrete>) {
    //         AUTOQ::Symbol::Concrete::mulmap[std::make_pair(ComplexParser(ctx->complex(0)->getText(), constants).getComplex(), ComplexParser(ctx->complex(1)->getText(), constants).getComplex())] = ComplexParser(ctx->complex(2)->getText(), constants).getComplex();
    //         // AUTOQ::Symbol::Concrete::mulmap[std::make_pair(ComplexParser(ctx->complex(1)->getText(), constants).getComplex(), ComplexParser(ctx->complex(0)->getText(), constants).getComplex())] = ComplexParser(ctx->complex(2)->getText(), constants).getComplex();
    //     } else if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Predicate>) {
    //         AUTOQ::Symbol::Predicate p[3];
    //         for (int i=0; i<3; i++) {
    //             auto str = ctx->complex(i)->getText();
    //             auto it = predicates.find(str);
    //             if (it == predicates.end())
    //                 p[i] = AUTOQ::Symbol::Predicate(str);
    //             else
    //                 p[i] = AUTOQ::Symbol::Predicate(it->second);
    //         }
    //         AUTOQ::Symbol::Predicate::mulmap[std::make_pair(p[0], p[1])] = p[2];
    //         // AUTOQ::Symbol::Predicate::mulmap[std::make_pair(p[1], p[0])] = p[2];
    //     } else if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Symbolic>) {
    //         AUTOQ::Symbol::Symbolic::mulmap[std::make_pair(AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(0)->getText(), constants).getSymbolicComplex()), AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(1)->getText(), constants).getSymbolicComplex()))] = AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(2)->getText(), constants).getSymbolicComplex());
    //         // AUTOQ::Symbol::Symbolic::mulmap[std::make_pair(AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(1)->getText(), constants).getSymbolicComplex()), AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(0)->getText(), constants).getSymbolicComplex()))] = AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(2)->getText(), constants).getSymbolicComplex());
    //     } else {
    //         THROW_AUTOQ_ERROR("This kind of symbol is still unsupported!");
    //     }
    //     return {};
    // }

    // std::any visitAccepted(ExtendedDiracParser::AcceptedContext *ctx) override {
    //     if (ctx->set().size() == 1) { // RULE: set
    //         return visit(ctx->set(0));
    //     } else { // RULE: set '\\' set
    //         // TODO:
    //         /*
    //         auto left = visit(ctx->set(0)); // Left operand
    //         auto right = visit(ctx->set(1)); // Right operand
    //         return visit(ctx->set(0)); //std::make_pair(left, right);
    //         */
    //        return {};
    //     }
    // }

    std::any visitExpr(ExtendedDiracParser::ExprContext *ctx) override {
        if (mode == EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT) {
            return std::any_cast<std::string>(visit(ctx->tset()));
        } else if (mode == SPLIT_TENSORED_EXPRESSION_INTO_VECTOR_OF_SETS_WITHOUT_TENSOR) {
            return std::any_cast<std::vector<std::string>>(visit(ctx->tset()));
        } else if (mode == COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES) {
            auto segment2strs = std::any_cast<segment2strs_t>(visit(ctx->tset()));
            segment2split_t segment2split;
            for (const auto &strs : segment2strs) { // loop through all tensor segments
                // one iteration = one tensor segment
                std::vector<unitsplit_t> allIntvls;
                for (const auto &strsplit : strs) {
                    // One strsplit contains intervals of many variable units.
                    // We want to take the union of all intervals of all strSsplit, and
                    // make sure that all intervals are either the same or disjoint.
                    for (const auto &intvl : strsplit) {
                        size_t i=0;
                        for (; i<allIntvls.size(); i++) {
                            if (intvl.second <= allIntvls.at(i).first) {
                                break;
                            }
                        }
                        // Now intvl should be inserted at the left of allIntvls[i] if no overlapping.
                        if (!(i==0 || allIntvls.at(i-1).second <= intvl.first)) {
                            if (allIntvls.at(i-1).first==intvl.first && allIntvls.at(i-1).second==intvl.second) {
                                continue; // This interval already exists in the pool!
                            }
                            THROW_AUTOQ_ERROR("Units not aligned!");
                        }
                        allIntvls.insert(allIntvls.begin()+i, intvl);
                    }
                }
                segment2split.push_back(allIntvls);
            }
            return segment2split;
        } else if (mode == REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT) {
            return std::any_cast<std::string>(visit(ctx->tset()));
        } else if (mode == COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION) {
            return std::any_cast<segment2perm_t>(visit(ctx->tset()));
        } else if (mode == REORDER_UNITS_BY_THE_GROUP) {
            return std::any_cast<std::string>(visit(ctx->tset()));
        } else if (mode == EVALUATE_EACH_SET_BRACES_TO_LSTA) {
            return visit(ctx->tset());
            // The type can be AUTOQ::Automata<Symbol> (without ;) or
            //                 std::pair<AUTOQ::Automata<Symbol>, AUTOQ::Automata<Symbol2>> (with ;)
        } else if (mode == SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS) {
            return std::any_cast<std::string>(visit(ctx->tset()));
        } else if (mode == SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY) {
            auto aut = std::any_cast<AUTOQ::Automata<AUTOQ::Symbol::Constrained>>(visit(ctx->tset()));
            auto do_the_work = [&]<typename SymbolV>() -> std::any {
                // TODO: Write a callable function for copying one automaton to another one with the transitions replaced.
                AUTOQ::Automata<SymbolV> result;
                result.name = aut.name;
                result.finalStates = aut.finalStates;
                result.stateNum = aut.stateNum;
                result.qubitNum = aut.qubitNum;
                result.vars = aut.vars;
                result.constraints = aut.constraints;
                result.hasLoop = aut.hasLoop;
                result.isTopdownDeterministic = aut.isTopdownDeterministic;
                result.gateCount = aut.gateCount;
                result.stateBefore = aut.stateBefore;
                result.transitionBefore = aut.transitionBefore;
                result.gateLog = aut.gateLog;
                result.opLog = aut.opLog;
                result.include_status = aut.include_status;
                result.binop_time = aut.binop_time;
                result.branch_rest_time = aut.branch_rest_time;
                result.value_rest_time = aut.value_rest_time;
                result.total_gate_time = aut.total_gate_time;
                result.total_removeuseless_time = aut.total_removeuseless_time;
                result.total_reduce_time = aut.total_reduce_time;
                result.total_include_time = aut.total_include_time;
                result.start_execute = aut.start_execute;
                result.stop_execute = aut.stop_execute;
                // typedef std::map<SymbolTag, std::map<State, std::set<StateVector>>> TopDownTransitions;
                // TopDownTransitions transitions;
                for (const auto &[st, v] : aut.transitions) { // st stands for SymbolTag.
                    typename AUTOQ::Automata<SymbolV>::SymbolTag st2;
                    if (st.is_internal()) {
                        st2 = typename AUTOQ::Automata<SymbolV>::SymbolTag(SymbolV(st.symbol().qubit()), st.tag());
                    } else {
                        const auto &c = st.symbol().complex;
                        if constexpr (std::is_same_v<SymbolV, AUTOQ::Symbol::Concrete>) {
                            if (c.size() == 0) { // a zero constant
                                st2 = AUTOQ::Automata<AUTOQ::Symbol::Concrete>::SymbolTag(AUTOQ::Symbol::Concrete(AUTOQ::Complex::Complex::Zero()), st.tag());
                            } else {
                                AUTOQ::Complex::Complex sum;
                                for (const auto &[termId, term] : c) {
                                    auto it = constants.find(std::get<0>(term));
                                    if (it == constants.end()) {
                                        if (do_not_throw_term_undefined_error) {
                                            encountered_term_undefined_error = true;
                                        } else {
                                            THROW_AUTOQ_ERROR("Constant " + std::get<0>(term) + " is not defined!");
                                        }
                                    } else {
                                        sum += it->second;
                                    }
                                }
                                st2 = AUTOQ::Automata<AUTOQ::Symbol::Concrete>::SymbolTag(AUTOQ::Symbol::Concrete(sum), st.tag());
                            }
                        } else if constexpr (std::is_same_v<SymbolV, AUTOQ::Symbol::Symbolic>) {
                            if (c.size() == 0) { // a zero constant
                                st2 = AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag(AUTOQ::Symbol::Symbolic(AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor(AUTOQ::Complex::Complex::Zero())), st.tag());
                            } else {
                                AUTOQ::Complex::SymbolicComplex sum;
                                for (const auto &[termId, term] : c) {
                                    auto it = constants.find(std::get<0>(term));
                                    if (it != constants.end()) {
                                        sum += AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor(it->second);
                                    } else {
                                        sum += AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor(std::get<0>(term), result.vars);
                                    }
                                }
                                st2 = AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag(AUTOQ::Symbol::Symbolic(sum), st.tag());
                            }
                        } else if constexpr (std::is_same_v<SymbolV, AUTOQ::Symbol::Predicate>) {
                            if (c.size() == 0) { // a true predicate
                                st2 = AUTOQ::Automata<AUTOQ::Symbol::Predicate>::SymbolTag(AUTOQ::Symbol::Predicate("true"), st.tag());
                            } else if (c.size() != 1) {
                                THROW_AUTOQ_ERROR("All leaves should be exactly one predicate.");
                            } else {
                                AUTOQ::Symbol::Predicate p;
                                for (const auto &[termId, term] : c) {
                                    p = AUTOQ::Symbol::Predicate(predicates.at(std::get<0>(term)));
                                    // use = because c.size() == 1
                                }
                                st2 = AUTOQ::Automata<AUTOQ::Symbol::Predicate>::SymbolTag(p, st.tag());
                            }
                        } else {
                            THROW_AUTOQ_ERROR("Unsupported symbol type!!!");
                        }
                    }
                    auto &to_be_put_into = result.transitions[st2];
                    for (const auto &[s, inS] : v) {
                        auto &to_be_put_into2 = to_be_put_into[s];
                        for (const auto &in : inS) {
                            to_be_put_into2.insert(in);
                        }
                    }
                }
                result.reduce();
                return result;
            };
            if (!switch_symbol_to_second) {
                return do_the_work.template operator()<Symbol>();
            } else {
                return do_the_work.template operator()<Symbol2>();
            }
        } else {
            THROW_AUTOQ_ERROR("Unsupported mode!");
        }
    }

    perm_t sortedConnectedComponent(const graph_t &edges) {
        std::map<int, std::vector<int>> graph;
        std::set<int> unvisited;
        // Build the undirected graph
        for (const auto& [u, v] : edges) {
            graph[u].push_back(v);
            graph[v].push_back(u);
            unvisited.insert(u);
            unvisited.insert(v);
        }
        // BFS to collect all reachable nodes from 'start'
        perm_t result;
        while (!unvisited.empty()) {
            std::set<int> visited;
            int start = *unvisited.begin();
            std::queue<int> q;
            q.push(start);
            visited.insert(start);
            unvisited.erase(start);
            while (!q.empty()) {
                int node = q.front(); q.pop();
                for (int neighbor : graph[node]) {
                    if (visited.count(neighbor) == 0) {
                        visited.insert(neighbor);
                        q.push(neighbor);
                    }
                }
            }
            // Copy to a vector and sort
            std::vector<int> cc(visited.begin(), visited.end());
            std::sort(cc.begin(), cc.end());
            result.insert(cc);
        }
        return result;
    }
    std::any visitTset(ExtendedDiracParser::TsetContext *ctx) override {
        if (mode == EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT) {
            if (ctx->op == nullptr) return std::any_cast<std::string>(visit(ctx->set(0)));
            if (ctx->op->getType() == ExtendedDiracParser::POWER) {
                int times = std::stoi(ctx->N->getText());
                std::string result;
                while ((times--) > 0) {
                    if (result.length() > 0) {
                        result += " ⊗ ";
                    }
                    result += std::any_cast<std::string>(visit(ctx->set(0)));
                }
                return result;
            }
            if (ctx->op->getType() == ExtendedDiracParser::PROD) return std::any_cast<std::string>(visit(ctx->tset(0))) + " ⊗ " + std::any_cast<std::string>(visit(ctx->tset(1)));
            THROW_AUTOQ_ERROR("Undefined grammar for tset!");
        } else if (mode == SPLIT_TENSORED_EXPRESSION_INTO_VECTOR_OF_SETS_WITHOUT_TENSOR) {
            if (ctx->op == nullptr) { // Notice that in this base case, we don't continue to visit, so we don't have to deal with this mode in the following nonterminals.
                std::vector<std::string> result;
                result.push_back(ctx->set(0)->getText());
                return result;
            }
            if (ctx->op->getType() == ExtendedDiracParser::PROD) {
                auto vec0 = std::any_cast<std::vector<std::string>>(visit(ctx->tset(0)));
                auto vec1 = std::any_cast<std::vector<std::string>>(visit(ctx->tset(1)));
                vec0.insert(vec0.end(), vec1.begin(), vec1.end());
                return vec0;
            }
            // Since set^N has been expanded in the first phase, there should be no power operators here.
            // Besides, we process one *.hsl at a time, so there should be no semicolon operators here.
            THROW_AUTOQ_ERROR("Undefined grammar for tset!");
        } else if (mode == COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES) {
            if (ctx->op == nullptr) {
                segment2strs_t segment2strs;
                segment2strs.push_back(std::any_cast<strs2split_t>(visit(ctx->set(0))));
                return segment2strs;
            } else if (ctx->op->getType() == ExtendedDiracParser::POWER) {
                THROW_AUTOQ_ERROR("Undefined grammar for tset!");
            } else if (ctx->op->getType() == ExtendedDiracParser::PROD) { // RULE: set op=PROD set
                THROW_AUTOQ_ERROR("Undefined grammar for tset!");
            } else if (ctx->op->getType() == ExtendedDiracParser::SEMICOLON) { // RULE: set op=SEMICOLON set
                segment2strs_t segment2strs;
                auto vec0 = std::any_cast<strs2split_t>(visit(ctx->set(0)));
                auto vec1 = std::any_cast<strs2split_t>(visit(ctx->set(1)));
                vec0.insert(vec0.end(), vec1.begin(), vec1.end());
                segment2strs.push_back(vec0);
                return segment2strs;
            } else {
                THROW_AUTOQ_ERROR("Undefined grammar for tset!");
            }
        } else if (mode == REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT) {
            if (ctx->op == nullptr) { // set
                currentSplit = segment2split.front(); // access the first element
                segment2split.erase(segment2split.begin()); // remove it (O(n) operation)
                return std::any_cast<std::string>(visit(ctx->set(0)));
            } else if (ctx->op->getType() == ExtendedDiracParser::SEMICOLON) { // set; set
                currentSplit = segment2split.front(); // access the first element
                segment2split.erase(segment2split.begin()); // remove it (O(n) operation)
                auto res1 = std::any_cast<std::string>(visit(ctx->set(0)));
                auto res2 = std::any_cast<std::string>(visit(ctx->set(1)));
                return res1 + " ; " + res2;
            } else if (ctx->op->getType() == ExtendedDiracParser::PROD) {
                std::string str0 = std::any_cast<std::string>(visit(ctx->tset(0)));
                std::string str1 = std::any_cast<std::string>(visit(ctx->tset(1)));
                return str0 + " ⊗ " + str1;
            } else {
                // since set^N has been expanded in the first phase, there should be no power operators here.
                THROW_AUTOQ_ERROR("Undefined grammar for tset!");
            }
        } else if (mode == COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION) {
            if (ctx->op == nullptr) { // only one segment
                segment2perm_t result;
                result.push_back(sortedConnectedComponent(std::any_cast<graph_t>(visit(ctx->set(0)))));
                return result;
            }
            if (ctx->op->getType() == ExtendedDiracParser::SEMICOLON) { // set; set
                auto graph1 = std::any_cast<graph_t>(visit(ctx->set(0)));
                auto graph2 = std::any_cast<graph_t>(visit(ctx->set(1)));
                graph1.insert(graph2.begin(), graph2.end());
                segment2perm_t result;
                result.push_back(sortedConnectedComponent(graph1));
                return result;
            }
            if (ctx->op->getType() == ExtendedDiracParser::PROD) {
                auto vec0 = std::any_cast<segment2perm_t>(visit(ctx->tset(0)));
                auto vec1 = std::any_cast<segment2perm_t>(visit(ctx->tset(1)));
                vec0.insert(vec0.end(), vec1.begin(), vec1.end());
                return vec0;
            }
            // since set^N has been expanded in the first phase, there should be no power operators here.
            THROW_AUTOQ_ERROR("Undefined grammar for tset!");
        } else if (mode == REORDER_UNITS_BY_THE_GROUP) {
            if (ctx->op == nullptr) {
                currentPerm = segment2perm.front(); // access the first element
                segment2perm.erase(segment2perm.begin()); // remove it (O(n) operation)
                return std::any_cast<std::string>(visit(ctx->set(0)));
            }
            if (ctx->op->getType() == ExtendedDiracParser::SEMICOLON) { // set; set
                currentPerm = segment2perm.front(); // access the first element
                segment2perm.erase(segment2perm.begin()); // remove it (O(n) operation)
                auto res1 = std::any_cast<std::string>(visit(ctx->set(0)));
                auto res2 = std::any_cast<std::string>(visit(ctx->set(1)));
                return res1 + " ; " + res2;
            }
            if (ctx->op->getType() == ExtendedDiracParser::PROD) {
                std::string str0 = std::any_cast<std::string>(visit(ctx->tset(0)));
                std::string str1 = std::any_cast<std::string>(visit(ctx->tset(1)));
                return str0 + " ⊗ " + str1;
            }
            // since set^N has been expanded in the first phase, there should be no power operators here.
            THROW_AUTOQ_ERROR("Undefined grammar for tset!");
        } else if (mode == EVALUATE_EACH_SET_BRACES_TO_LSTA) {
            if (ctx->op == nullptr) {
                currentPerm = segment2perm.front(); // access the first element
                segment2perm.erase(segment2perm.begin()); // remove it (O(n) operation)
                return std::any_cast<AUTOQ::Automata<Symbol>>(visit(ctx->set(0)));
            }
            if (ctx->op->getType() == ExtendedDiracParser::SEMICOLON) { // set; set
                auto aut0 = std::any_cast<AUTOQ::Automata<Symbol>>(visit(ctx->set(0)));
                auto constants_tmp = constants;
                constants = constants2;
                auto predicates_tmp = predicates;
                predicates = predicates2;
                switch_symbol_to_second = true; // switch to the second symbol type
                auto aut1 = std::any_cast<AUTOQ::Automata<Symbol2>>(visit(ctx->set(1)));
                switch_symbol_to_second = false; // switch back to the first symbol type
                constants = constants_tmp;
                predicates = predicates_tmp;
                return std::make_pair(aut0, aut1);
            }
            if (ctx->op->getType() == ExtendedDiracParser::PROD) {
                auto aut0 = std::any_cast<AUTOQ::Automata<Symbol>>(visit(ctx->tset(0)));
                auto aut1 = std::any_cast<AUTOQ::Automata<Symbol>>(visit(ctx->tset(1)));
                return aut0 * aut1;
            }
            // since set^N has been expanded in the first phase, there should be no power operators here.
            THROW_AUTOQ_ERROR("Undefined grammar for tset!");
        } else if (mode == SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS) { // we only decompose {diracs (: varcons)?}
            if (ctx->op != nullptr) {
                THROW_AUTOQ_ERROR("We only decompose {diracs (: varcons)?}");
            }
            return std::any_cast<std::string>(visit(ctx->set(0)));
        } else if (mode == SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY) {
            if (ctx->op == nullptr) {
                auto aut = std::any_cast<AUTOQ::Automata<AUTOQ::Symbol::Constrained>>(visit(ctx->set(0)));
                return aut;
            }
            if (ctx->op->getType() == ExtendedDiracParser::PROD) {
                auto aut0 = std::any_cast<AUTOQ::Automata<AUTOQ::Symbol::Constrained>>(visit(ctx->tset(0)));
                auto aut1 = std::any_cast<AUTOQ::Automata<AUTOQ::Symbol::Constrained>>(visit(ctx->tset(1)));
                return aut0 * aut1;
            }
            // since set^N has been expanded in the first phase, there should be no power operators here.
            THROW_AUTOQ_ERROR("Undefined grammar for tset!");
        } else {
            THROW_AUTOQ_ERROR("Unsupported mode!");
        }
    }

    std::any visitSet(ExtendedDiracParser::SetContext *ctx) override {
        if (mode == EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT) {
            if (ctx->op != nullptr) return std::any_cast<std::string>(visit(ctx->set(0))) + " ∪ " + std::any_cast<std::string>(visit(ctx->set(1)));
            std::string result;
            for (const auto &dirac : std::any_cast<std::vector<std::string>>(visit(ctx->diracs()))) {
                if (result.length() > 0) result += " ∪ ";
                result += "{" + dirac;
                result += (ctx->varcons() == nullptr) ? "" : (" : " + ctx->varcons()->getText());
                result += "}";
            }
            return result;
        } else if (mode == COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES) {
            if (ctx->op != nullptr) { // RULE: set op=UNION set
                auto vec0 = std::any_cast<strs2split_t>(visit(ctx->set(0)));
                auto vec1 = std::any_cast<strs2split_t>(visit(ctx->set(1)));
                vec0.insert(vec0.end(), vec1.begin(), vec1.end());
                return vec0;
            } else { // RULE: { diracs (: varcons)? }
                globalVar2len = (ctx->varcons() == nullptr) ? std::map<char, int>() : std::any_cast<std::map<char, int>>(visit(ctx->varcons()));
                return std::any_cast<strs2split_t>(visit(ctx->diracs())); // Vstrs
            }
        } else if (mode == REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT) {
            if (ctx->op != nullptr) { // RULE: set op=UNION set
                auto str1 = std::any_cast<std::string>(visit(ctx->set(0)));
                auto str2 = std::any_cast<std::string>(visit(ctx->set(1)));
                return str1 + " ∪ " + str2;
            }
            globalVar2len = (ctx->varcons() == nullptr) ? std::map<char, int>() : std::any_cast<std::map<char, int>>(visit(ctx->varcons()));
            usedVars = std::set<char>(); // reset usedVars
            for (const auto &[k, v] : globalVar2len) {
                usedVars.insert(k);
            }
            std::string result = "{" + std::any_cast<std::string>(visit(ctx->diracs())); // after expansion, diracs contains only one dirac.
            result += (ctx->varcons() == nullptr) ? "" : (" : " + ctx->varcons()->getText());
            result += "}";
            return result;
        } else if (mode == COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION) {
            if (ctx->op != nullptr) {
                auto graph1 = std::any_cast<graph_t>(visit(ctx->set(0)));
                auto graph2 = std::any_cast<graph_t>(visit(ctx->set(1)));
                for (const auto &edge : graph2) {
                    graph1.insert(edge);
                }
                return graph1;
            }

            // To compute the graph relation in {term + ... + term : varcons}, we
            // first collect, for each unit, all variables appearing in some term,
            // and then for each unordered pair (i, j) of unit indices, inspect if
            // there is one variable appearing in both variable pools, or there is
            // one inequality connecting two variables, one in one pool and the other
            // in the other pool.
            //
            // Before this phase, REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT
            // already not only distinguishes local variables from global variables,
            // but also distinguishes all local variables among different terms, so
            // we don't need to worry about name collisions here.
            auto relation = std::any_cast<relation_t>(visit(ctx->diracs())); // after expansion, diracs contains only one dirac.
            if (ctx->varcons() != nullptr) {
                auto ineqs = std::any_cast<ineqS_t>(visit(ctx->varcons()));
                for (const auto &ineq : ineqs) {
                    relation.second.insert(ineq);
                }
            }
            graph_t graph;
            for (size_t i=0; i<relation.first.size(); i++) {
                auto set1 = relation.first.at(i);
                for (size_t j=0; j<relation.first.size(); j++) {
                    auto set2 = relation.first.at(j);
                    for (char ch : set1) {
                        if (set2.find(ch) != set2.end()) {
                            graph.insert(std::make_pair(i, j)); // i < j
                            goto BOTTOM;
                        }
                    }
                    for (char ch : set2) {
                        if (set1.find(ch) != set1.end()) {
                            graph.insert(std::make_pair(i, j)); // i < j
                            goto BOTTOM;
                        }
                    }
                    for (const auto &ineq : relation.second) {
                        if ((set1.find(ineq.first.at(0)) != set1.end() && set2.find(ineq.second.at(0)) != set2.end()) ||
                            (set2.find(ineq.first.at(0)) != set2.end() && set1.find(ineq.second.at(0)) != set1.end())) {
                            graph.insert(std::make_pair(i, j)); // i < j
                            goto BOTTOM;
                        }
                    }
                    BOTTOM:;
                }
            }
            return graph;
        } else if (mode == REORDER_UNITS_BY_THE_GROUP) {
            if (ctx->op != nullptr) { // RULE: set op=UNION set
                auto str1 = std::any_cast<std::string>(visit(ctx->set(0)));
                auto str2 = std::any_cast<std::string>(visit(ctx->set(1)));
                return str1 + " ∪ " + str2;
            } else {
                std::string result = "{" + std::any_cast<std::string>(visit(ctx->diracs())); // after expansion, diracs contains only one dirac.
                result += (ctx->varcons() == nullptr) ? "" : (" : " + ctx->varcons()->getText());
                result += "}";
                return result;
            }
        } else if (mode == EVALUATE_EACH_SET_BRACES_TO_LSTA) {
            auto do_the_work = [&]<typename SymbolV>() -> std::any {
                if (ctx->op != nullptr) {
                    auto aut1 = std::any_cast<AUTOQ::Automata<SymbolV>>(visit(ctx->set(0)));
                    auto aut2 = std::any_cast<AUTOQ::Automata<SymbolV>>(visit(ctx->set(1)));
                    return aut1 || aut2;
                }
                EvaluationVisitor visitor(constants, predicates);
                visitor.mode = SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS;
                visitor.currentPerm = currentPerm;
                visitor.switch_symbol_to_second = switch_symbol_to_second;
                visitor.do_not_throw_term_undefined_error = do_not_throw_term_undefined_error;
                auto group_decomposition = std::any_cast<std::string>(visitor.let_visitor_parse_string(ctx->getText())); // {diracs (: varcons)?}
                visitor.mode = SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY;
                auto aut = visitor.let_visitor_parse_string(group_decomposition); // {diracs (: varcons)?} ⊗ {diracs (: varcons)?} ⊗ ...
                encountered_term_undefined_error = visitor.encountered_term_undefined_error;
                return aut;
            };
            if (!switch_symbol_to_second) {
                return do_the_work.template operator()<Symbol>();
            } else {
                return do_the_work.template operator()<Symbol2>();
            }
        } else if (mode == SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS) { // we only decompose {diracs (: varcons)?}
            if (ctx->op != nullptr) {
                THROW_AUTOQ_ERROR("We only decompose {diracs (: varcons)?}");
            }
            auto result = std::any_cast<std::vector<std::tuple<std::string, std::vector<varconS_t>, std::vector<std::string>>>>(visit(ctx->diracs()));
            std::vector<std::string> varconsS;
            varconS_t varcons2 = (ctx->varcons() == nullptr) ? varconS_t() : std::any_cast<varconS_t>(visit(ctx->varcons()));
            for (size_t i=0; i<std::get<2>(result.at(0)).size(); i++) { // .at(0) here is arbitrary
                varconsS.push_back("");
                for (const auto &varcon : varcons2) {
                    for (const auto &res : result) {
                        for (char v : std::get<2>(res).at(i)) {
                            if (varcon.first.find(std::tolower(v)) != varcon.first.end()) {
                                if (varconsS.back().length() > 0) {
                                    varconsS.back() += ", ";
                                }
                                varconsS.back() += varcon.second;
                                goto END;
                            }
                        }
                    }
                    END:;
                }
            }
            std::string output;
            for (size_t i=0; i<varconsS.size(); i++) { // i denotes the group number
                if (output.length() > 0) {
                    output += " ⊗ ";
                }
                output += "{";
                for (const auto &term : result) {
                    if (output.back() != '{') {
                        output += " + ";
                    }
                    output += std::get<0>(term);
                    auto localVarcons = std::get<1>(term).at(i);
                    bool isFirst = true;
                    for (const auto &varcon : localVarcons) {
                        if (isFirst) output += "∑";
                        else output += ", ";
                        output += varcon.second;
                        isFirst = false;
                    }
                    output += "|" + std::get<2>(term).at(i) + "⟩";
                }
                if (varconsS.at(i).length() > 0) {
                    output += " : " + varconsS.at(i);
                }
                output += "}";
            }
            return output; // {diracs (: varcons)?} ⊗ {diracs (: varcons)?} ⊗ ...
        } else if (mode == SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY) { // { c1 |u1u2u3> + c2 ∑ vc2 |u1u2u3> + ... : vcG }
            if (ctx->op != nullptr) {
                THROW_AUTOQ_ERROR("There should be no UNION in SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY mode.");
            }
            AUTOQ::Automata<AUTOQ::Symbol::Constrained> autAll;
            auto terms = std::any_cast<std::vector<std::tuple<std::string, std::optional<std::tuple<int, std::set<char>, ineqS_t, eqs_t>>, std::string>>>(visit(ctx->diracs()));
            auto vc_global = (ctx->varcons() == nullptr) ? std::tuple<int, std::set<char>, ineqS_t, eqs_t>()
                                                         : std::any_cast<std::tuple<int, std::set<char>, ineqS_t, eqs_t>>(visit(ctx->varcons()));
            auto num_qubits = (ctx->varcons() == nullptr) ? std::get<0>(std::get<1>(*terms.begin()).value()) : std::get<0>(vc_global);
            for (int q=0; q<num_qubits; q++) { // one qubit, one LSTA, and we finally tensor them all.
                AUTOQ::Automata<AUTOQ::Symbol::Constrained> autQ;
                std::map<char, std::string> var2value;
                for (const auto &eq : std::get<3>(vc_global)) {
                    var2value[eq.first] = eq.second;
                }
                //////////////////////////////
                std::map<char, int> var2index;
                auto vars = std::get<1>(vc_global);
                for (char v : vars) {
                    var2index[v] = var2index.size();
                }
                auto mAx = (1 << vars.size()); // one value corresponds to one Dirac state
                auto stdget2vc_global = std::vector<std::pair<std::string, std::string>>(std::get<2>(vc_global).begin(), std::get<2>(vc_global).end()); // ensure order
                for (int enumeration_counter = 0; enumeration_counter < mAx; enumeration_counter++) {
                    std::map<std::string, AUTOQ::Complex::ConstrainedComplex> dirac; // one value corresponds to one Dirac state
                    /************************************************/
                    // construct global predicates for the coefficient
                    std::vector<bool> gp;
                    for (const auto &ineq : stdget2vc_global) { // std::cout << ineq.first << "≠" << ineq.second;
                        auto lhs = (enumeration_counter >> var2index.at(ineq.first.at(0))) & 1;
                        int rhs;
                        if (ineq.second.at(0) == '0' || ineq.second.at(0) == '1') { // constant string
                            rhs = ineq.second.at(q) - '0'; // convert to the usual number data type
                        } else { // also a variable
                            rhs = (enumeration_counter >> var2index.at(ineq.second.at(0))) & 1;
                        }
                        if (lhs != rhs) { gp.push_back(true); /*+= "T";*/ } else { gp.push_back(false); /*+= "F";*/ }
                    }
                    /************************************************/
                    int termId = 0;
                    for (const auto &term : terms) { // no equalities should occur in a term
                        std::map<char, int> localvar2index;
                        auto localVarcons = std::get<1>(term).has_value() ? std::get<1>(term).value() : std::tuple<int, std::set<char>, ineqS_t, eqs_t>();
                        auto localVars = std::get<1>(localVarcons);
                        for (char v : localVars) {
                            localvar2index[v] = localvar2index.size();
                        }
                        auto localConst2Val = std::get<3>(localVarcons);
                        auto localmAx = (1 << localVars.size()); // should expand the summation
                        auto stdget2vc_local = std::vector<std::pair<std::string, std::string>>(std::get<2>(localVarcons).begin(), std::get<2>(localVarcons).end()); // ensure order
                        for (int local_counter = 0; local_counter < localmAx; local_counter++) {
                            std::vector<bool> lp;
                            for (const auto &ineq : stdget2vc_local) { // std::cout << ineq.first << "≠" << ineq.second;
                                // Notice that if this inequality connects one local variable and one global variable,
                                // the local variable may be on the left hand side or the right hand side.
                                int lhs, rhs;
                                auto it = localvar2index.find(ineq.first.at(0));
                                if (it != localvar2index.end()) { // LHS is a local variable.
                                    lhs = (local_counter >> (it->second)) & 1;
                                    if (ineq.second.at(0) == '0' || ineq.second.at(0) == '1') { // constant string
                                        rhs = ineq.second.at(q) - '0'; // convert to the usual number data type
                                    } else {
                                        auto it2 = localvar2index.find(ineq.second.at(0));
                                        if (it2 != localvar2index.end()) { // RHS is a local variable
                                            rhs = (local_counter >> (it2->second)) & 1;
                                        } else { // RHS is a global variable
                                            rhs = (enumeration_counter >> var2index.at(ineq.second.at(0))) & 1;
                                        }
                                    }
                                } else { // LHS is a global variable
                                    lhs = (enumeration_counter >> var2index.at(ineq.first.at(0))) & 1;
                                    rhs = (local_counter >> localvar2index.at(ineq.second.at(0))) & 1;
                                }
                                if (lhs != rhs) { lp.push_back(true); /*+= "T";*/ } else { lp.push_back(false); /*+= "F";*/ }
                            }
                            std::string ket;
                            auto body = std::get<2>(term);
                            for (char ch : body) {
                                int val; /* bool type: can only be 0 or 1 */
                                auto ch2 = static_cast<char>(std::tolower(ch));
                                auto it = localvar2index.find(ch2);
                                if (it != localvar2index.end()) { // is a local variable
                                    val = ((local_counter >> (it->second)) & 1);
                                } else {
                                    auto it3 = localConst2Val.find(ch2);
                                    if (it3 != localConst2Val.end()) { // is a local constant
                                        val = it3->second.at(q) - '0'; // convert to the usual
                                    } else {
                                        auto it2 = var2index.find(ch2);
                                        if (it2 != var2index.end()) { // is a global variable
                                            val = ((enumeration_counter >> (it2->second)) & 1);
                                        } else { // is a global constant
                                            val = var2value.at(ch2).at(q) - '0';
                                        }
                                    }
                                }
                                if (ch2 != ch) {
                                    ket += '0' + (1 - val); // convert to the usual number data type
                                } else {
                                    ket += '0' + val; // convert to the usual number data type
                                }
                            }
                            dirac[ket] += AUTOQ::Complex::ConstrainedComplex(termId, std::get<0>(term), gp, lp);
                        }
                        termId++;
                    }
                    autQ = autQ || efficiently_construct_singleton_lsta(dirac);
                }
                if (q == 0) {
                    autAll = autQ;
                } else {
                    autAll = autAll * autQ;
                }
            }
            autAll.fraction_simplification();
            autAll.reduce();
            return autAll;
        } else {
            THROW_AUTOQ_ERROR("Unsupported mode!");
        }
    }

    std::any visitDiracs(ExtendedDiracParser::DiracsContext *ctx) override {
        if (mode == EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT) {
            std::vector<std::string> result;
            if (ctx->diracs() != nullptr) { // RULE: diracs, dirac
                result = std::any_cast<std::vector<std::string>>(visit(ctx->diracs()));
            }
            result.push_back(std::any_cast<std::string>(visit(ctx->dirac())));
            return result;
        } else if (mode == COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES) {
            if (ctx->diracs() == nullptr) { // RULE: dirac
                return std::any_cast<strs2split_t>(visit(ctx->dirac()));
            } else { // RULE: diracs ',' dirac
                auto vec0 = std::any_cast<strs2split_t>(visit(ctx->diracs()));
                auto vec1 = std::any_cast<strs2split_t>(visit(ctx->dirac()));
                vec0.insert(vec0.end(), vec1.begin(), vec1.end());
                return vec0;
            }
        } else if (mode == REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT) {
            if (ctx->diracs() == nullptr) { // RULE: dirac
                return visit(ctx->dirac());
            } else { // RULE: diracs ',' dirac
                return std::any_cast<AUTOQ::Automata<Symbol>>(visit(ctx->diracs())) || std::any_cast<AUTOQ::Automata<Symbol>>(visit(ctx->dirac()));
            }
        } else if (mode == COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION) {
            if (ctx->diracs() != nullptr) { // RULE: diracs, dirac
                THROW_AUTOQ_ERROR("After expansion, diracs should contain only one dirac.");
            }
            return std::any_cast<relation_t>(visit(ctx->dirac()));
        } else if (mode == REORDER_UNITS_BY_THE_GROUP) {
            if (ctx->diracs() != nullptr) { // RULE: diracs, dirac
                THROW_AUTOQ_ERROR("After expansion, diracs should contain only one dirac.");
            }
            return std::any_cast<std::string>(visit(ctx->dirac()));
        } else if (mode == SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS) {
            if (ctx->diracs() != nullptr) { // RULE: diracs, dirac
                THROW_AUTOQ_ERROR("After expansion, diracs should contain only one dirac.");
            }
            return std::any_cast<std::vector<std::tuple<std::string, std::vector<varconS_t>, std::vector<std::string>>>>(visit(ctx->dirac()));
        } else if (mode == SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY) {
            if (ctx->diracs() != nullptr) { // RULE: diracs, dirac
                THROW_AUTOQ_ERROR("After expansion, diracs should contain only one dirac.");
            }
            return std::any_cast<std::vector<std::tuple<std::string, std::optional<std::tuple<int, std::set<char>, ineqS_t, eqs_t>>, std::string>>>(visit(ctx->dirac()));
        } else {
            THROW_AUTOQ_ERROR("Unsupported mode!");
        }
    }

    std::any visitDirac(ExtendedDiracParser::DiracContext *ctx) override {
        if (mode == EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT) {
            if (ctx->dirac() == nullptr) { // RULE: term
                    return std::any_cast<std::string>(visit(ctx->term()));
            } else { // RULE: dirac + term
                auto str1 = std::any_cast<std::string>(visit(ctx->dirac()));
                auto str2 = std::any_cast<std::string>(visit(ctx->term()));
                return str1 + " + " + str2;
            }
        } else if (mode == COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES) {
            if (ctx->dirac() == nullptr) { // RULE: term
                strs2split_t Vstrs;
                Vstrs.push_back(std::any_cast<strsplit_t>(visit(ctx->term())));
                return Vstrs;
            } else { // RULE: dirac + term
                auto Vstrs = std::any_cast<strs2split_t>(visit(ctx->dirac()));
                Vstrs.push_back(std::any_cast<strsplit_t>(visit(ctx->term())));
                return Vstrs;
            }
        } else if (mode == REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT) {
            if (ctx->dirac() == nullptr) { // RULE: term
                return std::any_cast<std::string>(visit(ctx->term()));
            } else { // RULE: dirac + term
                auto str1 = std::any_cast<std::string>(visit(ctx->dirac()));
                auto str2 = std::any_cast<std::string>(visit(ctx->term()));
                return str1 + " + " + str2;
            }
        } else if (mode == COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION) {
            if (ctx->dirac() == nullptr) { // RULE: term
                return std::any_cast<relation_t>(visit(ctx->term()));
            } else { // RULE: dirac + term
                auto relation1 = std::any_cast<relation_t>(visit(ctx->dirac()));
                auto relation2 = std::any_cast<relation_t>(visit(ctx->term()));
                int i = 0;
                for (const auto &chars: relation2.first) {
                    relation1.first.at(i).insert(*chars.begin());
                    i++;
                }
                for (const auto &ineq: relation2.second) {
                    relation1.second.insert(ineq);
                }
                return relation1;
            }
        } else if (mode == REORDER_UNITS_BY_THE_GROUP) {
            if (ctx->dirac() == nullptr) { // RULE: term
                return std::any_cast<std::string>(visit(ctx->term()));
            } else { // RULE: dirac + term
                auto str1 = std::any_cast<std::string>(visit(ctx->dirac()));
                auto str2 = std::any_cast<std::string>(visit(ctx->term()));
                return str1 + " + " + str2;
            }
        } else if (mode == SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS) {
            if (ctx->dirac() == nullptr) { // RULE: term
                std::vector<std::tuple<std::string, std::vector<varconS_t>, std::vector<std::string>>> result;
                result.push_back(std::any_cast<std::tuple<std::string, std::vector<varconS_t>, std::vector<std::string>>>(visit(ctx->term())));
                return result;
            } else { // RULE: dirac + term
                auto result1 = std::any_cast<std::vector<std::tuple<std::string, std::vector<varconS_t>, std::vector<std::string>>>>(visit(ctx->dirac()));
                auto result2 = std::any_cast<std::tuple<std::string, std::vector<varconS_t>, std::vector<std::string>>>(visit(ctx->term()));
                result1.push_back(result2);
                return result1;
            }
        } else if (mode == SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY) {
            if (ctx->dirac() == nullptr) { // RULE: term
                std::vector<std::tuple<std::string, std::optional<std::tuple<int, std::set<char>, ineqS_t, eqs_t>>, std::string>> result;
                result.push_back(std::any_cast<std::tuple<std::string, std::optional<std::tuple<int, std::set<char>, ineqS_t, eqs_t>>, std::string>>(visit(ctx->term())));
                return result;
            } else { // RULE: dirac + term
                auto result1 = std::any_cast<std::vector<std::tuple<std::string, std::optional<std::tuple<int, std::set<char>, ineqS_t, eqs_t>>, std::string>>>(visit(ctx->dirac()));
                auto result2 = std::any_cast<std::tuple<std::string, std::optional<std::tuple<int, std::set<char>, ineqS_t, eqs_t>>, std::string>>(visit(ctx->term()));
                result1.push_back(result2);
                return result1;
            }
        } else {
            THROW_AUTOQ_ERROR("Unsupported mode!");
        }
    }

    std::any visitTerm(ExtendedDiracParser::TermContext *ctx) override {
        if (mode == EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT) {
            auto vstr = ctx->VStr->getText();
            std::string vstr2;
            for (size_t i=0; i<vstr.length(); i++) {
                if (i+1<vstr.length() && vstr.at(i+1)=='\'') {
                    vstr2.push_back(vstr.at(i)-'a'+'A'); // capitalize the bit complement
                    i++;
                } else {
                    vstr2.push_back(vstr.at(i));
                }
            }
            if (ctx->varcons() == nullptr) { // C=STR BAR VStr=STR RIGHT_ANGLE_BRACKET
                return std::any_cast<std::string>(ctx->C->getText() + "|" + vstr2 + "⟩");
            } else { // C=STR SUM varcons BAR VStr=STR RIGHT_ANGLE_BRACKET
                return std::any_cast<std::string>(ctx->C->getText() + "∑" + ctx->varcons()->getText() + "|" + vstr2 + "⟩");
            }
        } else if (mode == COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES) {
            strsplit_t intervals;
            std::map<char, int> localVar2len;
            if (ctx->varcons() != nullptr) {
                localVar2len = std::any_cast<std::map<char, int>>(visit(ctx->varcons()));
            }
            int len = 0;
            for (const auto &c : ctx->VStr->getText()) {
                if ((c == '0') || (c == '1')) {
                    len++;
                    continue;
                }
                auto it = localVar2len.find(static_cast<char>(std::tolower(c)));
                if (it != localVar2len.end()) {
                    intervals.push_back(unitsplit_t(len, len+it->second));
                    len += it->second;
                } else {
                    it = globalVar2len.find(static_cast<char>(std::tolower(c)));
                    if (it != globalVar2len.end()) {
                        intervals.push_back(unitsplit_t(len, len+it->second));
                        len += it->second;
                    } else {
                        THROW_AUTOQ_ERROR("Undefined variable!");
                    }
                }
            }
            return intervals;
        } else if (mode == REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT) {
            /***************************************************************/
            // Check if there is some local variable using global characters.
            // If yes, then we need to change the local variable's name.
            std::map<char, int> localVar2len;
            if (ctx->varcons() != nullptr) {
                localVar2len = std::any_cast<std::map<char, int>>(visit(ctx->varcons()));
            }
            std::map<char, char> changeLocalVar2;
            for (const auto &[k, v] : localVar2len) {
                if (usedVars.find(k) == usedVars.end()) { // if this local variable has not been used before,
                    usedVars.insert(k); // keep the original name
                } else { // otherwise,
                    for (char newCh = 'a'; newCh <= 'z'; newCh++) { // Find a new character for this local variable
                        if (usedVars.find(newCh) == usedVars.end()) {
                            changeLocalVar2[k] = newCh;
                            usedVars.insert(newCh);
                            break;
                        }
                        if (newCh == 'z') {
                            THROW_AUTOQ_ERROR("chars not enough!!!");
                        }
                    }
                }
            }
            /***************************************************************/
            std::string vstr = ctx->VStr->getText();
            std::string vstr2; // the rewritten output
            remember_the_lengths_of_each_unit_position.clear();
            /*************************************************/
            currentSplit_t completeCurrentSplit; // fill the gaps such that all units except the last are covered
            int connectionIndex = 0;
            for (const auto &[l, r] : currentSplit) {
                if (connectionIndex < l) {
                    completeCurrentSplit.push_back(unitsplit_t(connectionIndex, l));
                }
                completeCurrentSplit.push_back(unitsplit_t(l, r));
                connectionIndex = r;
            }
            completeCurrentSplit.push_back(unitsplit_t(connectionIndex, -1)); // indicate checking the last remaining part not classified as a unit (if it exists)
            /***********************************************/
            std::map<std::string, char> localVal2const;
            for (const auto &[l, r] : completeCurrentSplit) {
                if (r == -1 || // the last remaining part not classified as a unit must be a constant
                    vstr.at(0)=='0' || vstr.at(0)=='1') {
                    if (vstr.empty()) continue; // reject if there is no remaining part
                    std::string this_constant_string = ((r == -1) ? vstr : vstr.substr(0, r-l));
                    if (!std::all_of(this_constant_string.begin(), this_constant_string.end(), [](char ch) { return ch == '0' || ch == '1'; })) {
                        THROW_AUTOQ_ERROR("Not aligned!");
                    }
                    if (r != -1) vstr.erase(0, r-l);
                    auto it = localVal2const.find(this_constant_string);
                    if (it != localVal2const.end()) {
                        vstr2 += it->second;
                    } else {
                        // Find a character for this constant!
                        char ch='a';
                        for (; ch<='z'; ch++) {
                            if (usedVars.find(ch) == usedVars.end()) {
                                usedVars.insert(ch);
                                break;
                            }
                            if (ch == 'z') {
                                THROW_AUTOQ_ERROR("chars not enough!!!");
                            }
                        }
                        vstr2 += ch;
                        localVal2const[this_constant_string] = ch;
                    }
                    remember_the_lengths_of_each_unit_position.push_back(this_constant_string.length());
                } else { // char or CHAR
                    char ch = std::tolower(vstr.at(0)); // IMPORTANT!
                    auto it = globalVar2len.find(static_cast<char>(ch));
                    if (it != globalVar2len.end()) { // is a global variable, whose name cannot be changed
                        vstr2 += vstr.at(0);
                        remember_the_lengths_of_each_unit_position.push_back(it->second);
                    } else { // must be a local variable
                        auto it = localVar2len.find(static_cast<char>(ch));
                        if (it == localVar2len.end()) {
                            THROW_AUTOQ_ERROR("Undefined variable!");
                        } else if (it->second != r - l) {
                            THROW_AUTOQ_ERROR("Not aligned!");
                        } else { // check if it has already been renamed
                            auto it2 = changeLocalVar2.find(ch);
                            if (it2 == changeLocalVar2.end()) { // not renamed
                                vstr2 += vstr.at(0);
                            } else { // has been renamed
                                if (vstr.at(0) == ch) { // lowercase
                                    vstr2 += vstr.at(0);
                                } else { // uppercase (bit complemented)
                                    vstr2 += it2->second - 'a' + 'A';
                                }
                            }
                            remember_the_lengths_of_each_unit_position.push_back(it->second);
                        }
                    }
                    vstr.erase(vstr.begin());
                }
            }

            // C=STR BAR VStr=STR RIGHT_ANGLE_BRACKET
            // C=STR SUM varcons BAR VStr=STR RIGHT_ANGLE_BRACKET
            // two rules processed together
            auto vc = (ctx->varcons() == nullptr) ? "" : ctx->varcons()->getText(); // may contain capitalized bit complement
            auto ket = vstr2;
            for (auto *str : {&vc, &ket}) {
                for (auto &ch : *str) {
                    auto it = changeLocalVar2.find(static_cast<char>(std::tolower(ch)));
                    if (it != changeLocalVar2.end()) {
                        if (std::isupper(ch)) {
                            ch = it->second - 'a' + 'A';
                        } else { // std::islower(ch)
                            ch = it->second;
                        }
                    }
                }
            }
            for (const auto &[c, v] : localVal2const) {
                if (vc.empty()) {
                    vc += std::string{v} + "=" + c;
                } else {
                    vc += ", " + std::string{v} + "=" + c;
                }
            }
            return ctx->C->getText() + "∑" + vc + "|" + ket + "⟩";
        } else if (mode == COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION) {
            unit2vars_t first;
            auto str = ctx->VStr->getText();
            for (auto ch : str) {
                first.push_back(vars_t{static_cast<char>(std::tolower(ch))});
            }
            ineqS_t second;
            if (ctx->varcons() != nullptr) {
                second = std::any_cast<ineqS_t>(visit(ctx->varcons()));
            }
            return relation_t{first, second};
        } else if (mode == REORDER_UNITS_BY_THE_GROUP) {
            std::string vstr = ctx->VStr->getText();
            std::vector<bool> moved(vstr.length(), false);
            std::string vstr2;
            for (size_t i=0; i<vstr.length(); i++) {
                if (!moved.at(i)) {
                    for (const auto &cc : currentPerm) {
                        if (std::find(cc.begin(), cc.end(), i) != cc.end()) {
                            for (auto j : cc) {
                                vstr2.push_back(vstr.at(j));
                                moved.at(j) = true;
                            }
                            break;
                        }
                    }
                    if (!moved.at(i)) { // NOTE: This patch deals with the case when a character is not in any connected component.
                        vstr2.push_back(vstr.at(i));
                        moved.at(i) = true;
                    }
                }
            }
            if (ctx->varcons() == nullptr) { // C=STR BAR VStr=STR RIGHT_ANGLE_BRACKET
                return std::any_cast<std::string>(ctx->C->getText() + "|" + vstr2 + "⟩");
            } else { // C=STR SUM varcons BAR VStr=STR RIGHT_ANGLE_BRACKET
                return std::any_cast<std::string>(ctx->C->getText() + "∑" + ctx->varcons()->getText() + "|" + vstr2 + "⟩");
            }
        } else if (mode == SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS) {
            auto vecVarconS2 = ctx->varcons() == nullptr ? varconS_t() : std::any_cast<varconS_t>(visit(ctx->varcons()));
            std::vector<varconS_t> vecVarconS;
            std::vector<std::string> groups;
            auto vstr = ctx->VStr->getText();
            std::vector<int> selectedCC;
            for (size_t i=0; i < vstr.length(); i += selectedCC.size()) {
                selectedCC.clear();
                for (const auto &cc : currentPerm) { // Notice that the indices in currentPerm are no longer valid here. We only want those "fixpoint" indices!
                    if (std::find(cc.begin(), cc.end(), i) != cc.end()) {
                        selectedCC = cc; // find the connected component that contains the index i
                        break; // one index belongs to at most one connected component
                    }
                }
                if (selectedCC.empty()) { // this character is a group itself
                    selectedCC = {static_cast<int>(i)};
                } // NOTE: This patch deals with the case when a character is not in any connected component.
                auto str = vstr.substr(i, selectedCC.size());
                varconS_t varconS;
                for (char ch : str) {
                    ch = std::tolower(ch);
                    for (const auto &varcon : vecVarconS2) {
                        /* varcon: BAR V=STR BAR EQ N=STR {isNonZero($N.text)}?
                                    | V=STR EQ CStr=STR
                                    | ineq
                                    ;
                        */
                        if (varcon.first.find(ch) != varcon.first.end()) {
                            varconS.push_back(varcon);
                        }
                    }
                }
                vecVarconS.push_back(varconS);
                groups.push_back(str);
            }
            return std::make_tuple(ctx->C->getText(), vecVarconS, groups);
        } else if (mode == SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY) {
            // std::tuple<std::string, std::optional<std::tuple<int, std::set<char>, ineqS_t, eqs_t>>, std::string>
            //            coefficient,                varcons: <len,   control vars,     inequalities>,          ket>
            auto coefficient = ctx->C->getText();
            std::optional<std::tuple<int, std::set<char>, ineqS_t, eqs_t>> varcons;
            auto ket = ctx->VStr->getText();
            if (ctx->varcons() != nullptr) {
                varcons = std::any_cast<std::tuple<int, std::set<char>, ineqS_t, eqs_t>>(visit(ctx->varcons()));
            }
            return std::make_tuple(coefficient, varcons, ket);
        } else {
            THROW_AUTOQ_ERROR("Unsupported mode!");
        }
    }

    std::any visitVarcons(ExtendedDiracParser::VarconsContext *ctx) override {
        if (mode == COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES ||
            mode == REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT) {
            if (ctx->varcons() == nullptr) { // RULE: varcon
                return std::any_cast<std::map<char, int>>(visit(ctx->varcon()));
            } else { // RULE: varcons ',' varcon
                auto result = std::any_cast<std::map<char, int>>(visit(ctx->varcons())); // previous
                auto present = std::any_cast<std::map<char, int>>(visit(ctx->varcon()));
                if (!present.empty()) {
                    if (result.find(present.begin()->first) == result.end()) {
                        result[present.begin()->first] = present.begin()->second;
                    } else {
                        THROW_AUTOQ_ERROR("The same index is used more than once!");
                    }
                }
                return result;
            }
        } else if (mode == COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION) {
            if (ctx->varcons() == nullptr) { // RULE: varcon
                return std::any_cast<ineqS_t>(visit(ctx->varcon()));
            } else { // RULE: varcons ',' varcon
                auto result = std::any_cast<ineqS_t>(visit(ctx->varcons())); // previous
                auto present = std::any_cast<ineqS_t>(visit(ctx->varcon()));
                for (const auto &pair : present) {
                    result.insert(pair);
                }
                return result;
            }
        } else if (mode == SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS) {
            if (ctx->varcons() == nullptr) { // RULE: varcon
                varconS_t result;
                result.push_back(std::any_cast<varcon_t>(visit(ctx->varcon())));
                return result;
            } else { // RULE: varcons ',' varcon
                auto result = std::any_cast<varconS_t>(visit(ctx->varcons())); // previous
                auto present = std::any_cast<varcon_t>(visit(ctx->varcon()));
                result.push_back(present);
                return result;
            }
        } else if (mode == SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY) {
            // std::tuple<int, std::set<char>, ineqS_t, eqs_t>
            //  varcons: <len,   control vars,     inequalities>
            std::tuple<int, std::set<char>, ineqS_t, eqs_t> result;
            if (ctx->varcons() != nullptr) { // RULE: varcons ',' varcon
                result = std::any_cast<std::tuple<int, std::set<char>, ineqS_t, eqs_t>>(visit(ctx->varcons())); // previous
            }
            auto varcon = visit(ctx->varcon());
            const std::type_info &type = varcon.type();
            if (type == typeid(std::pair<char, int>)) {
                std::get<0>(result) = std::any_cast<std::pair<char, int>>(varcon).second;
                std::get<1>(result).insert(std::any_cast<std::pair<char, int>>(varcon).first);
            } else if (type == typeid(ineq_t)) {
                std::get<2>(result).insert(std::any_cast<ineq_t>(varcon));
            } else { // if (type == typeid(eq_t)) {
                auto eq = std::any_cast<eq_t>(varcon);
                std::get<0>(result) = eq.second.length();
                std::get<3>(result)[eq.first] = eq.second;
            }
            return result;
        } else {
            THROW_AUTOQ_ERROR("Unsupported mode!");
        }
    }

    std::any visitVarcon(ExtendedDiracParser::VarconContext *ctx) override {
        if (mode == COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES ||
            mode == REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT) {
            if (ctx->ineq() != nullptr) {
                return std::map<char, int>();
            } else if (ctx->N != nullptr) { // RULE: BAR V=NAME BAR EQ N=DIGITS
                std::string var = ctx->V->getText();
                if (var.length() == 1) {
                    int len = std::stoi(ctx->N->getText());
                    return std::map<char, int>{{var[0], len}};
                } else {
                    THROW_AUTOQ_ERROR("The index must be a single character!");
                }
            } else if (ctx->CStr != nullptr) { // RULE: V=NAME EQ CStr=DIGITS
                return std::map<char, int>();
            } else {
                THROW_AUTOQ_ERROR("Unexpected varcon format!");
            }
        } else if (mode == COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION) {
            if (ctx->ineq() == nullptr) {
                return ineqS_t();
            }
           return std::any_cast<ineqS_t>(visit(ctx->ineq()));
        } else if (mode == SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS) {
            if (ctx->ineq() == nullptr) {
                std::string var = ctx->V->getText();
                if (var.length() != 1) {
                    THROW_AUTOQ_ERROR("Variables must be a single character!");
                }
                return varcon_t{{var[0]}, ctx->getText()};
            }
            return std::any_cast<varcon_t>(visit(ctx->ineq()));
        } else if (mode == SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY) {
            if (ctx->ineq() == nullptr) {
                if (ctx->N != nullptr) { // RULE: BAR V=NAME BAR EQ N=DIGITS
                    return std::make_pair(ctx->V->getText().at(0), std::stoi(ctx->N->getText()));
                } else { //  RULE: V=NAME EQ CStr=DIGITS
                    return std::make_pair(ctx->V->getText().at(0), ctx->CStr->getText());
                }
            } else {
                return std::any_cast<ineq_t>(visit(ctx->ineq()));
            }
        } else {
            THROW_AUTOQ_ERROR("Unsupported mode!");
        }
    }

    std::any visitIneq(ExtendedDiracParser::IneqContext *ctx) override {
        if (mode == COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES ||
            mode == REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT ||
            mode == COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION) {
            ineqS_t set;
            auto text = ctx->R->getText();
            if (text.length() == 1 && 'a' <= text.at(0) && text.at(0) <= 'z') {
                set.insert(ineq_t(std::minmax(ctx->L->getText(), text)));
                return set;
            } else {
                return set;
            }
        } else if (mode == SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS) {
            std::set<char> vars;
            if (ctx->L->getText().length() != 1) {
                THROW_AUTOQ_ERROR("Variables should be characters!");
            }
            vars.insert(static_cast<char>(std::tolower(ctx->L->getText().at(0))));
            auto text = ctx->R->getText();
            if (text.length() == 1 && 'a' <= text.at(0) && text.at(0) <= 'z') {
                vars.insert(static_cast<char>(std::tolower(text.at(0))));
            }
            return varcon_t{vars, ctx->getText()};
        } else if (mode == SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY) {
            auto text = ctx->R->getText();
            if (text.length() == 1 && 'a' <= text.at(0) && text.at(0) <= 'z') {
                return ineq_t(std::minmax(ctx->L->getText(), text));
            } else {
                return ineq_t(ctx->L->getText(), ctx->R->getText());
            }
        } else {
            THROW_AUTOQ_ERROR("Unsupported mode!");
        }
    }
};
