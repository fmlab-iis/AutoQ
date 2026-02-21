/* Included inside EvaluationVisitor. Do not include directly. */
    /* -------- VisitVarcons, VisitVarcon, VisitEq, VisitIneq: variables and constraints (varcons, varcon, eq, ineq) -------- */
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
            } else if (ctx->eq() != nullptr) { // RULE: V=NAME EQ CStr=DIGITS
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
                std::string var;
                if (ctx->V != nullptr) {
                    var = ctx->V->getText();
                } else {
                    var = std::any_cast<std::string>(visit(ctx->eq()));
                }
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
                    return visit(ctx->eq());
                }
            } else {
                return std::any_cast<ineq_t>(visit(ctx->ineq()));
            }
        } else {
            THROW_AUTOQ_ERROR("Unsupported mode!");
        }
    }

    std::any visitEq(ExtendedDiracParser::EqContext *ctx) override {
        if (mode == COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES ||
            mode == REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT ||
            mode == SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY) {
            auto V = ctx->complex(0)->getText();
            if (!(V.length() == 1 && 'a' <= V.at(0) && V.at(0) <= 'z')) THROW_AUTOQ_ERROR("V should be a lower case letter here.");
            auto CStr = ctx->complex(1)->getText();
            if (!std::all_of(CStr.begin(), CStr.end(), [](char c) { return c == '0' || c == '1'; })) THROW_AUTOQ_ERROR("CStr should be a binary string here.");
            return std::make_pair(V.at(0), CStr);
        } else if (mode == SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS) {
            return ctx->complex(0)->getText();
        } else { // ConstraintParser
            return (std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))).realToSMT(z3Ctx) == std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(1))).realToSMT(z3Ctx) &&
                    std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))).imagToSMT(z3Ctx) == std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(1))).imagToSMT(z3Ctx)).simplify();
        }
    }

    std::any visitIneq(ExtendedDiracParser::IneqContext *ctx) override {
        if (mode == COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES ||
            mode == REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT ||
            mode == COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION) {
            // isALowercaseLetter($L.text) && (isALowercaseLetter($R.text) || isAConstantBinaryString($R.text))
            auto L = ctx->complex(0)->getText();
            if (!(L.length() == 1 && 'a' <= L.at(0) && L.at(0) <= 'z')) THROW_AUTOQ_ERROR("L should be a lower case letter here.");
            auto R = ctx->complex(1)->getText();
            if (!((R.length() == 1 && 'a' <= R.at(0) && R.at(0) <= 'z') || std::all_of(R.begin(), R.end(), [](char c) { return c == '0' || c == '1'; }))) THROW_AUTOQ_ERROR("R should be a lower case letter or a binary string here.");
            ineqS_t set;
            if (R.length() == 1 && 'a' <= R.at(0) && R.at(0) <= 'z') {
                set.insert(ineq_t(std::minmax(L, R)));
                return set;
            } else {
                return set;
            }
        } else if (mode == SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS) {
            // isALowercaseLetter($L.text) && (isALowercaseLetter($R.text) || isAConstantBinaryString($R.text))
            auto L = ctx->complex(0)->getText();
            if (!(L.length() == 1 && 'a' <= L.at(0) && L.at(0) <= 'z')) THROW_AUTOQ_ERROR("L should be a lower case letter here.");
            auto R = ctx->complex(1)->getText();
            if (!((R.length() == 1 && 'a' <= R.at(0) && R.at(0) <= 'z') || std::all_of(R.begin(), R.end(), [](char c) { return c == '0' || c == '1'; }))) THROW_AUTOQ_ERROR("R should be a lower case letter or a binary string here.");
            std::set<char> vars;
            if (L.length() != 1) {
                THROW_AUTOQ_ERROR("Variables should be characters!");
            }
            vars.insert(static_cast<char>(std::tolower(L.at(0))));
            if (R.length() == 1 && 'a' <= R.at(0) && R.at(0) <= 'z') {
                vars.insert(static_cast<char>(std::tolower(R.at(0))));
            }
            return varcon_t{vars, ctx->getText()};
        } else if (mode == SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY) {
            // isALowercaseLetter($L.text) && (isALowercaseLetter($R.text) || isAConstantBinaryString($R.text))
            auto L = ctx->complex(0)->getText();
            if (!(L.length() == 1 && 'a' <= L.at(0) && L.at(0) <= 'z')) THROW_AUTOQ_ERROR("L should be a lower case letter here.");
            auto R = ctx->complex(1)->getText();
            if (!((R.length() == 1 && 'a' <= R.at(0) && R.at(0) <= 'z') || std::all_of(R.begin(), R.end(), [](char c) { return c == '0' || c == '1'; }))) THROW_AUTOQ_ERROR("R should be a lower case letter or a binary string here.");
            if (R.length() == 1 && 'a' <= R.at(0) && R.at(0) <= 'z') {
                return ineq_t(std::minmax(L, R));
            } else {
                return ineq_t(L, R);
            }
        } else {
            return (std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))).realToSMT(z3Ctx) != std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(1))).realToSMT(z3Ctx) ||
                    std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))).imagToSMT(z3Ctx) != std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(1))).imagToSMT(z3Ctx)).simplify();
            THROW_AUTOQ_ERROR("Unsupported mode!");
        }
    }

