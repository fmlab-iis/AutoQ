/* Included inside EvaluationVisitor. Do not include directly. */
    /* -------- VisitPredicate: predicate / SMT expressions (eq, ineq, <, <=, >, >=, !, &&, ||) -------- */
    std::any visitPredicate(ExtendedDiracParser::PredicateContext *ctx) override {
        if (ctx->eq() != nullptr) return visit(ctx->eq());
        else if (ctx->ineq() != nullptr) return visit(ctx->ineq());
        else if (ctx->LESS_THAN() != nullptr) {
            return (std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))).realToSMT(z3Ctx) < std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(1))).realToSMT(z3Ctx) &&
                    std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))).imagToSMT(z3Ctx) == 0 &&
                    std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(1))).imagToSMT(z3Ctx) == 0).simplify();
        } else if (ctx->LESS_EQUAL() != nullptr) {
            return (std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))).realToSMT(z3Ctx) <= std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(1))).realToSMT(z3Ctx) &&
                    std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))).imagToSMT(z3Ctx) == 0 &&
                    std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(1))).imagToSMT(z3Ctx) == 0).simplify();
        } else if (ctx->RIGHT_ANGLE_BRACKET() != nullptr) {
            return (std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))).realToSMT(z3Ctx) > std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(1))).realToSMT(z3Ctx) &&
                    std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))).imagToSMT(z3Ctx) == 0 &&
                    std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(1))).imagToSMT(z3Ctx) == 0).simplify();
        } else if (ctx->GREATER_EQUAL() != nullptr) {
            return (std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))).realToSMT(z3Ctx) >= std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(1))).realToSMT(z3Ctx) &&
                    std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))).imagToSMT(z3Ctx) == 0 &&
                    std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(1))).imagToSMT(z3Ctx) == 0).simplify();
        } else if (ctx->LOGICAL_NOT() != nullptr) {
            return (!std::any_cast<z3::expr>(visit(ctx->predicate(0)))).simplify();
        } else if (ctx->LOGICAL_AND() != nullptr) {
            return (std::any_cast<z3::expr>(visit(ctx->predicate(0))) && std::any_cast<z3::expr>(visit(ctx->predicate(1)))).simplify();
        } else if (ctx->LOGICAL_OR() != nullptr) {
            return (std::any_cast<z3::expr>(visit(ctx->predicate(0))) || std::any_cast<z3::expr>(visit(ctx->predicate(1)))).simplify();
        } else {
            return visit(ctx->predicate(0));
        }
    }
