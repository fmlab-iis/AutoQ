/* Included inside EvaluationVisitor. Do not include directly. */
    std::any visitExpr(ExtendedDiracParser::ExprContext *ctx) override {
        switch (mode) {
            case EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT:
                return visitExpr_expand(ctx);
            case SPLIT_TENSORED_EXPRESSION_INTO_VECTOR_OF_SETS_WITHOUT_TENSOR:
                return visitExpr_split(ctx);
            case COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES:
                return visitExpr_collectKets(ctx);
            case REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT:
                return std::any_cast<std::string>(visit(ctx->tset(0)));
            case COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION:
                return std::any_cast<segment2perm_t>(visit(ctx->tset(0)));
            case REORDER_UNITS_BY_THE_GROUP:
                return std::any_cast<std::string>(visit(ctx->tset(0)));
            case EVALUATE_EACH_SET_BRACES_TO_LSTA:
                return visit(ctx->tset(0));
            case SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS:
                return std::any_cast<std::string>(visit(ctx->tset(0)));
            case SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY:
                return visitExpr_shuffle(ctx);
            default:
                THROW_AUTOQ_ERROR("Unsupported mode!");
        }
    }

    std::any visitExpr_expand(ExtendedDiracParser::ExprContext *ctx) {
        if (ctx->SETMINUS() == nullptr) {
            return std::any_cast<std::string>(visit(ctx->tset(0)));
        }
        THROW_AUTOQ_ERROR("We currently do not support the SETMINUS operator!");
    }

    std::any visitExpr_split(ExtendedDiracParser::ExprContext *ctx) {
        if (ctx->SETMINUS() == nullptr) {
            return visit(ctx->tset(0));
        }
        THROW_AUTOQ_ERROR("We currently do not support the SETMINUS operator!");
    }

    std::any visitExpr_collectKets(ExtendedDiracParser::ExprContext *ctx) {
        auto segment2strs = std::any_cast<segment2strs_t>(visit(ctx->tset(0)));
        segment2split_t segment2split;
        for (const auto &strs : segment2strs) {
            std::vector<unitsplit_t> allIntvls;
            for (const auto &strsplit : strs) {
                for (const auto &intvl : strsplit) {
                    size_t i = 0;
                    for (; i < allIntvls.size(); i++) {
                        if (intvl.second <= allIntvls.at(i).first) break;
                    }
                    if (!(i == 0 || allIntvls.at(i - 1).second <= intvl.first)) {
                        if (allIntvls.at(i - 1).first == intvl.first && allIntvls.at(i - 1).second == intvl.second)
                            continue;
                        THROW_AUTOQ_ERROR("Units not aligned!");
                    }
                    allIntvls.insert(allIntvls.begin() + i, intvl);
                }
            }
            segment2split.push_back(allIntvls);
        }
        return segment2split;
    }

    std::any visitExpr_shuffle(ExtendedDiracParser::ExprContext *ctx) {
        auto aut = std::any_cast<AUTOQ::Automata<AUTOQ::Symbol::Constrained>>(visit(ctx->tset(0)));
            auto do_the_work = [&]<typename SymbolV>() -> std::any {
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
                for (const auto &[st, v] : aut.transitions) {
                    typename AUTOQ::Automata<SymbolV>::SymbolTag st2;
                    if (st.is_internal()) {
                        st2 = typename AUTOQ::Automata<SymbolV>::SymbolTag(SymbolV(st.symbol().qubit()), st.tag());
                    } else {
                        const auto &c = st.symbol().complex;
                        if constexpr (std::is_same_v<SymbolV, AUTOQ::Symbol::Concrete>) {
                            if (c.size() == 0) {
                                st2 = AUTOQ::Automata<AUTOQ::Symbol::Concrete>::SymbolTag(AUTOQ::Symbol::Concrete(AUTOQ::Complex::Complex::Zero()), st.tag());
                            } else {
                                AUTOQ::Complex::Complex sum;
                                for (const auto &[termId, term] : c) {
                                    auto cp = ComplexParser(std::get<0>(term), constants);
                                    if (!cp.getConstName().empty()) {
                                        if (tolerate_undefined_term) {
                                            encountered_undefined_term = true;
                                        } else {
                                            THROW_AUTOQ_ERROR("Constant " + std::get<0>(term) + " is not defined!");
                                        }
                                    } else {
                                        sum += cp.getComplex();
                                    }
                                }
                                st2 = AUTOQ::Automata<AUTOQ::Symbol::Concrete>::SymbolTag(AUTOQ::Symbol::Concrete(sum), st.tag());
                            }
                        } else if constexpr (std::is_same_v<SymbolV, AUTOQ::Symbol::Symbolic>) {
                            if (c.size() == 0) {
                                st2 = AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag(AUTOQ::Symbol::Symbolic(AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor(AUTOQ::Complex::Complex::Zero())), st.tag());
                            } else {
                                AUTOQ::Complex::SymbolicComplex sum;
                                for (const auto &[termId, term] : c) {
                                    auto scp = SymbolicComplexParser(std::get<0>(term), constants);
                                    sum += scp.getSymbolicComplex();
                                    auto scpgetNewVars = scp.getNewVars();
                                    result.vars.insert(scpgetNewVars.begin(), scpgetNewVars.end());
                                }
                                st2 = AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag(AUTOQ::Symbol::Symbolic(sum), st.tag());
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
    }
