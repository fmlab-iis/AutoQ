// Included inside struct EvaluationVisitor { ... } — visitScset.

    /* -------- VisitScset: semicolon-separated sets (scset → set | scset; set) -------- */
    std::any visitScset(ExtendedDiracParser::ScsetContext *ctx) override {
        if (mode == EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT) {
            if (ctx->SEMICOLON() != nullptr) {
                THROW_AUTOQ_ERROR("Semicolons are not expected in EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT!");
            }
            return std::any_cast<std::string>(visit(ctx->set()));
        } else if (mode == SPLIT_TENSORED_EXPRESSION_INTO_VECTOR_OF_SETS_WITHOUT_TENSOR) {
            if (ctx->SEMICOLON() != nullptr) {
                THROW_AUTOQ_ERROR("Semicolons are not expected in SPLIT_TENSORED_EXPRESSION_INTO_VECTOR_OF_SETS_WITHOUT_TENSOR!");
            }
            std::vector<std::string> result;
            result.push_back(ctx->set()->getText());
            return result;
        } else if (mode == COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES) {
            if (ctx->SEMICOLON() == nullptr) {
                return std::any_cast<strs2split_t>(visit(ctx->set()));
            } else {
                auto vec0 = std::any_cast<strs2split_t>(visit(ctx->scset()));
                auto vec1 = std::any_cast<strs2split_t>(visit(ctx->set()));
                vec0.insert(vec0.end(), vec1.begin(), vec1.end());
                return vec0;
            }
        } else if (mode == REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT) {
            if (ctx->SEMICOLON() == nullptr) { // set
                return std::any_cast<std::string>(visit(ctx->set()));
            } else {
                auto result = std::any_cast<std::string>(visit(ctx->scset()));
                result += " ; " + std::any_cast<std::string>(visit(ctx->set()));
                return result;
            }
        } else if (mode == COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION) {
            if (ctx->SEMICOLON() == nullptr) { // only one segment
                return visit(ctx->set());
            } else {
                auto graph1 = std::any_cast<graph_t>(visit(ctx->scset()));
                auto graph2 = std::any_cast<graph_t>(visit(ctx->set()));
                graph1.insert(graph2.begin(), graph2.end());
                return graph1;
            }
        } else if (mode == REORDER_UNITS_BY_THE_GROUP) {
            if (ctx->SEMICOLON() == nullptr) {
                return visit(ctx->set());
            } else {
                auto res1 = std::any_cast<std::string>(visit(ctx->scset()));
                auto res2 = std::any_cast<std::string>(visit(ctx->set()));
                return res1 + " ; " + res2;
            }
        } else if (mode == EVALUATE_EACH_SET_BRACES_TO_LSTA) {
            if (ctx->SEMICOLON() == nullptr) {
                std::vector<AUTOQ::Automata<Symbol>> result;
                result.push_back(std::any_cast<AUTOQ::Automata<Symbol>>(visit(ctx->set())));
                return result;
            } else {
                auto constants_last = constantsVector.back();
                constantsVector.pop_back();
                auto predicateConstraints_last = predicateConstraintsVector.back();
                predicateConstraintsVector.pop_back();
                auto vec = std::any_cast<std::vector<AUTOQ::Automata<Symbol>>>(visit(ctx->scset()));
                auto constants_tmp = constants;
                constants = constants_last;
                auto predicateConstraints_tmp = predicateConstraints;
                predicateConstraints = predicateConstraints_last;
                auto aut = std::any_cast<AUTOQ::Automata<Symbol>>(visit(ctx->set()));
                constants = constants_tmp;
                predicateConstraints = predicateConstraints_tmp;
                vec.push_back(aut);
                return vec;
            }
        } else if (mode == SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS) {
            if (ctx->SEMICOLON() != nullptr) {
                THROW_AUTOQ_ERROR("Semicolons are not expected in SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS!");
            }
            return std::any_cast<std::string>(visit(ctx->set()));
        } else if (mode == SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY) {
            if (ctx->SEMICOLON() != nullptr) {
                THROW_AUTOQ_ERROR("Semicolons are not expected in SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY!");
            }
            auto aut = std::any_cast<AUTOQ::Automata<AUTOQ::Symbol::Constrained>>(visit(ctx->set()));
            return aut;
        } else {
            THROW_AUTOQ_ERROR("Unsupported mode!");
        }
    }
