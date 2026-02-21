// Included inside struct EvaluationVisitor { ... } — visitTset.

    /* -------- VisitTset: tensor product (tset → scset | set^N | tset ⊗ tset) -------- */
    std::any visitTset(ExtendedDiracParser::TsetContext *ctx) override {
        if (mode == EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT) {
            if (ctx->scset() != nullptr) return std::any_cast<std::string>(visit(ctx->scset()));
            if (ctx->POWER() != nullptr) {
                int times = std::stoi(ctx->N->getText());
                std::string result;
                while ((times--) > 0) {
                    if (result.length() > 0) {
                        result += " ⊗ ";
                    }
                    result += std::any_cast<std::string>(visit(ctx->set()));
                }
                return result;
            }
            if (ctx->MUL() != nullptr || ctx->PROD() != nullptr) return std::any_cast<std::string>(visit(ctx->tset(0))) + " ⊗ " + std::any_cast<std::string>(visit(ctx->tset(1)));
            THROW_AUTOQ_ERROR("Undefined grammar for tset!");
        } else if (mode == SPLIT_TENSORED_EXPRESSION_INTO_VECTOR_OF_SETS_WITHOUT_TENSOR) {
            if (ctx->scset() != nullptr) { // Notice that in this base case, we don't continue to visit, so we don't have to deal with this mode in the following nonterminals.
                std::vector<std::string> result;
                result.push_back(ctx->scset()->getText());
                return result;
            }
            if (ctx->MUL() != nullptr || ctx->PROD() != nullptr) {
                auto vec0 = std::any_cast<std::vector<std::string>>(visit(ctx->tset(0)));
                auto vec1 = std::any_cast<std::vector<std::string>>(visit(ctx->tset(1)));
                vec0.insert(vec0.end(), vec1.begin(), vec1.end());
                return vec0;
            }
            // Since set^N has been expanded in the first phase, there should be no power operators here.
            // Besides, we process one *.hsl at a time, so there should be no semicolon operators here.
            THROW_AUTOQ_ERROR("Undefined grammar for tset!");
        } else if (mode == COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES) {
            if (ctx->scset() != nullptr) {
                segment2strs_t segment2strs;
                segment2strs.push_back(std::any_cast<strs2split_t>(visit(ctx->scset())));
                return segment2strs;
            } else if (ctx->POWER() != nullptr) {
                THROW_AUTOQ_ERROR("Should not appear after EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT!");
            } else if (ctx->MUL() != nullptr || ctx->PROD() != nullptr) { // RULE: set op=PROD set
                auto vec0 = std::any_cast<segment2strs_t>(visit(ctx->tset(0)));
                auto vec1 = std::any_cast<segment2strs_t>(visit(ctx->tset(1)));
                vec0.insert(vec0.end(), vec1.begin(), vec1.end());
                return vec0;
            } else {
                THROW_AUTOQ_ERROR("Undefined grammar for tset!");
            }
        } else if (mode == REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT) {
            if (ctx->scset() != nullptr) { // set
                currentSplit = segment2split.front(); // access the first element
                segment2split.erase(segment2split.begin()); // remove it (O(n) operation)
                return std::any_cast<std::string>(visit(ctx->scset()));
            } else if (ctx->MUL() != nullptr || ctx->PROD() != nullptr) {
                std::string str0 = std::any_cast<std::string>(visit(ctx->tset(0)));
                std::string str1 = std::any_cast<std::string>(visit(ctx->tset(1)));
                return str0 + " ⊗ " + str1;
            } else {
                THROW_AUTOQ_ERROR("Undefined grammar for tset!");
            }
        } else if (mode == COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION) {
            if (ctx->scset() != nullptr) { // only one segment
                segment2perm_t result;
                result.push_back(sortedConnectedComponent(std::any_cast<graph_t>(visit(ctx->scset()))));
                return result;
            }
            if (ctx->MUL() != nullptr || ctx->PROD() != nullptr) {
                auto vec0 = std::any_cast<segment2perm_t>(visit(ctx->tset(0)));
                auto vec1 = std::any_cast<segment2perm_t>(visit(ctx->tset(1)));
                vec0.insert(vec0.end(), vec1.begin(), vec1.end());
                return vec0;
            }
            THROW_AUTOQ_ERROR("Undefined grammar for tset!");
        } else if (mode == REORDER_UNITS_BY_THE_GROUP) {
            if (ctx->scset() != nullptr) {
                currentPerm = segment2perm.front(); // access the first element
                segment2perm.erase(segment2perm.begin()); // remove it (O(n) operation)
                return std::any_cast<std::string>(visit(ctx->scset()));
            }
            if (ctx->MUL() != nullptr || ctx->PROD() != nullptr) {
                std::string str0 = std::any_cast<std::string>(visit(ctx->tset(0)));
                std::string str1 = std::any_cast<std::string>(visit(ctx->tset(1)));
                return str0 + " ⊗ " + str1;
            }
            THROW_AUTOQ_ERROR("Undefined grammar for tset!");
        } else if (mode == EVALUATE_EACH_SET_BRACES_TO_LSTA) {
            if (ctx->scset() != nullptr) {
                currentPerm = segment2perm.front(); // access the first element
                segment2perm.erase(segment2perm.begin()); // remove it (O(n) operation)
                return std::any_cast<std::vector<AUTOQ::Automata<Symbol>>>(visit(ctx->scset()));
            }
            if (ctx->MUL() != nullptr || ctx->PROD() != nullptr) {
                auto autVec0 = std::any_cast<std::vector<AUTOQ::Automata<Symbol>>>(visit(ctx->tset(0)));
                auto autVec1 = std::any_cast<std::vector<AUTOQ::Automata<Symbol>>>(visit(ctx->tset(1)));
                if (autVec0.size() != 1 || autVec1.size() != 1) {
                    THROW_AUTOQ_ERROR("We expect only one automaton in each vector here!");
                }
                return std::vector<AUTOQ::Automata<Symbol>>({autVec0.at(0) * autVec1.at(0)});
            }
            THROW_AUTOQ_ERROR("Undefined grammar for tset!");
        } else if (mode == SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS) { // we only decompose {diracs (: varcons)?}
            if (ctx->scset() == nullptr) {
                THROW_AUTOQ_ERROR("We only decompose {diracs (: varcons)?}");
            }
            return std::any_cast<std::string>(visit(ctx->scset()));
        } else if (mode == SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY) {
            if (ctx->scset() != nullptr) {
                auto aut = std::any_cast<AUTOQ::Automata<AUTOQ::Symbol::Constrained>>(visit(ctx->scset()));
                return aut;
            }
            if (ctx->MUL() != nullptr || ctx->PROD() != nullptr) {
                auto aut0 = std::any_cast<AUTOQ::Automata<AUTOQ::Symbol::Constrained>>(visit(ctx->tset(0)));
                auto aut1 = std::any_cast<AUTOQ::Automata<AUTOQ::Symbol::Constrained>>(visit(ctx->tset(1)));
                return aut0 * aut1;
            }
            THROW_AUTOQ_ERROR("Undefined grammar for tset!");
        } else {
            THROW_AUTOQ_ERROR("Unsupported mode!");
        }
    }
