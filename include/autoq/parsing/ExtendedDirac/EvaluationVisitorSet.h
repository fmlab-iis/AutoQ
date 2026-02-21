// Included inside struct EvaluationVisitor { ... } — visitSet.

    /* -------- VisitSet: brace-enclosed set ({ diracs }) -------- */
    std::any visitSet(ExtendedDiracParser::SetContext *ctx) override {
        if (mode == EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT) {
            if (ctx->UNION() != nullptr) {
                return std::any_cast<std::string>(visit(ctx->set(0))) + " ∪ " + std::any_cast<std::string>(visit(ctx->set(1)));
            } else {
                std::string result;
                for (const auto &dirac : std::any_cast<std::vector<std::string>>(visit(ctx->diracs()))) {
                    if (result.length() > 0) result += " ∪ ";
                    result += "{" + dirac;
                    result += (ctx->varcons() == nullptr) ? "" : (" : " + ctx->varcons()->getText());
                    result += "}";
                }
                return result;
            }
        } else if (mode == COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES) {
            if (ctx->UNION() != nullptr) { // RULE: set op=UNION set
                auto vec0 = std::any_cast<strs2split_t>(visit(ctx->set(0)));
                auto vec1 = std::any_cast<strs2split_t>(visit(ctx->set(1)));
                vec0.insert(vec0.end(), vec1.begin(), vec1.end());
                return vec0;
            } else { // RULE: { diracs (: varcons)? }
                globalVar2len = (ctx->varcons() == nullptr) ? std::map<char, int>() : std::any_cast<std::map<char, int>>(visit(ctx->varcons()));
                return std::any_cast<strs2split_t>(visit(ctx->diracs())); // Vstrs
            }
        } else if (mode == REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT) {
            if (ctx->UNION() != nullptr) { // RULE: set op=UNION set
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
            if (ctx->UNION() != nullptr) {
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
            if (ctx->UNION() != nullptr) { // RULE: set op=UNION set
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
                if (ctx->UNION() != nullptr) {
                    auto aut1 = std::any_cast<AUTOQ::Automata<SymbolV>>(visit(ctx->set(0)));
                    auto aut2 = std::any_cast<AUTOQ::Automata<SymbolV>>(visit(ctx->set(1)));
                    return aut1 || aut2;
                }
                EvaluationVisitor visitor({constants}, {predicateConstraints});
                visitor.mode = SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS;
                visitor.currentPerm = currentPerm;
                visitor.switch_symbol_to_second = switch_symbol_to_second;
                visitor.do_not_throw_term_undefined_error = do_not_throw_term_undefined_error;
                auto group_decomposition = std::any_cast<std::string>(visitor.let_visitor_parse_string(ctx->getText())); // {diracs (: varcons)?}
                visitor.mode = SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY;
                auto aut = std::any_cast<AUTOQ::Automata<SymbolV>>(visitor.let_visitor_parse_string(group_decomposition)); // {diracs (: varcons)?} ⊗ {diracs (: varcons)?} ⊗ ...
                encountered_term_undefined_error |= visitor.encountered_term_undefined_error;
                return aut;
            };
            if (!switch_symbol_to_second) {
                return do_the_work.template operator()<Symbol>();
            } else {
                return do_the_work.template operator()<Symbol2>();
            }
        } else if (mode == SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS) { // we only decompose {diracs (: varcons)?}
            if (ctx->UNION() != nullptr) {
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
            if (ctx->UNION() != nullptr) {
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
                    autQ = autQ || AUTOQ::ConstrainedAutomata::efficiently_construct_singleton_lsta(dirac);
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
