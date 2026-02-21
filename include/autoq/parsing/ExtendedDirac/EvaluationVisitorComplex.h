/* Included inside EvaluationVisitor. Do not include directly. */
    /* -------- VisitComplex: complex number parsing (independent of main grammar) -------- */
    Complex fastPower(Complex base, int exponent) {
        assert(exponent >= 0);
        if (exponent == 0) return 1;
        if (exponent % 2 == 0) {
            Complex temp = fastPower(base, exponent / 2);
            return temp * temp;
        } else {
            Complex temp = fastPower(base, (exponent - 1) / 2);
            return base * temp * temp;
        }
    }
    AUTOQ::Complex::SymbolicComplex fastPower(AUTOQ::Complex::SymbolicComplex base, int exponent) {
        assert(exponent >= 0);
        if (exponent == 0) {
            return AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor(1);
        }
        if (exponent % 2 == 0) {
            AUTOQ::Complex::SymbolicComplex temp = fastPower(base, exponent / 2);
            return temp * temp;
        } else {
            AUTOQ::Complex::SymbolicComplex temp = fastPower(base, (exponent - 1) / 2);
            return base * temp * temp;
        }
    }
    std::any visitComplex(ExtendedDiracParser::ComplexContext *ctx) override {
        if (ctx->n != nullptr) {
            if (mode == CONCRETE_COMPLEX) return fastPower(std::any_cast<Complex>(visit(ctx->complex(0))), std::stoi(ctx->n->getText()));
            if (mode == SYMBOLIC_COMPLEX) return fastPower(std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))), std::stoi(ctx->n->getText()));
            THROW_AUTOQ_ERROR("Unsupported mode!");
        } else if (ctx->sub != nullptr) {
            if (mode == CONCRETE_COMPLEX) return std::any_cast<Complex>(visit(ctx->complex(0))) * -1;
            if (mode == SYMBOLIC_COMPLEX) return std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))) * -1;
            THROW_AUTOQ_ERROR("Unsupported mode!");
        } else if (ctx->op != nullptr) {
            if (ctx->op->getType() == ExtendedDiracParser::MUL) {
                if (mode == CONCRETE_COMPLEX) return std::any_cast<Complex>(visit(ctx->complex(0))) * std::any_cast<Complex>(visit(ctx->complex(1)));
                if (mode == SYMBOLIC_COMPLEX) return std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))) * std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(1)));
                THROW_AUTOQ_ERROR("Unsupported mode!");
            } else if (ctx->op->getType() == ExtendedDiracParser::DIV) {
                if (mode == CONCRETE_COMPLEX) return std::any_cast<Complex>(visit(ctx->complex(0))) / std::any_cast<Complex>(visit(ctx->complex(1)));
                if (mode == SYMBOLIC_COMPLEX) {
                    auto b = std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(1)));
                    if (b.isConst()) {
                        return std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))) / b.to_complex();
                    }
                }
                THROW_AUTOQ_ERROR("Unsupported mode!");
            } else if (ctx->op->getType() == ExtendedDiracParser::ADD) {
                if (mode == CONCRETE_COMPLEX) return std::any_cast<Complex>(visit(ctx->complex(0))) + std::any_cast<Complex>(visit(ctx->complex(1)));
                if (mode == SYMBOLIC_COMPLEX) return std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))) + std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(1)));
                THROW_AUTOQ_ERROR("Unsupported mode!");
            } else if (ctx->op->getType() == ExtendedDiracParser::SUB) {
                if (mode == CONCRETE_COMPLEX) return std::any_cast<Complex>(visit(ctx->complex(0))) - std::any_cast<Complex>(visit(ctx->complex(1)));
                if (mode == SYMBOLIC_COMPLEX) return std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))) - std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(1)));
                THROW_AUTOQ_ERROR("Unsupported mode!");
            } else {
                THROW_AUTOQ_ERROR("Unsupported operator!");
            }
        } else if (ctx->func != nullptr) {
            if (ctx->func->getText() == "ei2pi") {
                if (mode == CONCRETE_COMPLEX) return Complex::Angle(std::any_cast<Complex>(visit(ctx->complex(0))).to_rational());
                if (mode == SYMBOLIC_COMPLEX) return AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor(Complex::Angle(std::any_cast<Complex>(visit(ctx->complex(0))).to_rational()));
                THROW_AUTOQ_ERROR("Unsupported mode!");
            } else if (ctx->func->getText() == "eipi") {
                if (mode == CONCRETE_COMPLEX) return Complex::Angle(std::any_cast<Complex>(visit(ctx->complex(0))).to_rational() / 2);
                if (mode == SYMBOLIC_COMPLEX) return AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor(Complex::Angle(std::any_cast<Complex>(visit(ctx->complex(0))).to_rational() / 2));
                THROW_AUTOQ_ERROR("Unsupported mode!");
            } else if (ctx->func->getText() == "real") {
                if (mode == CONCRETE_COMPLEX) return std::any_cast<Complex>(visit(ctx->complex(0))).real();
                if (mode == SYMBOLIC_COMPLEX) return std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))).real();
                THROW_AUTOQ_ERROR("Unsupported mode!");
            } else if (ctx->func->getText() == "imag") {
                if (mode == CONCRETE_COMPLEX) return std::any_cast<Complex>(visit(ctx->complex(0))).imag();
                if (mode == SYMBOLIC_COMPLEX) return std::any_cast<AUTOQ::Complex::SymbolicComplex>(visit(ctx->complex(0))).imag();
                THROW_AUTOQ_ERROR("Unsupported mode!");
            } else {
                THROW_AUTOQ_ERROR("Unsupported function " + ctx->func->getText() + "!");
            }
        } else if (ctx->complex().size() == 1) {
            return visit(ctx->complex(0));
        } else if (ctx->var != nullptr) {
            const auto &text = ctx->var->getText();
            if (std::all_of(text.begin(), text.end(), [](char c) { return '0' <= c && c <= '9'; })) {
                if (mode == CONCRETE_COMPLEX) return Complex(boost::multiprecision::cpp_int(text));
                if (mode == SYMBOLIC_COMPLEX) return AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor(Complex(boost::multiprecision::cpp_int(text)));
                THROW_AUTOQ_ERROR("Unsupported mode!");
            } else {
                auto it = constants.find(text);
                if (it != constants.end()) {
                    if (mode == CONCRETE_COMPLEX) return it->second;
                    if (mode == SYMBOLIC_COMPLEX) return AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor(it->second);
                    THROW_AUTOQ_ERROR("Unsupported mode!");
                } else if (text == "i") {
                    if (mode == CONCRETE_COMPLEX) return Complex::Angle(boost::rational<boost::multiprecision::cpp_int>(1, 4));
                    if (mode == SYMBOLIC_COMPLEX) return AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor(Complex::Angle(boost::rational<boost::multiprecision::cpp_int>(1, 4)));
                    THROW_AUTOQ_ERROR("Unsupported mode!");
                } else if (text == "sqrt2") {
                    if (mode == CONCRETE_COMPLEX) return Complex::sqrt2();
                    if (mode == SYMBOLIC_COMPLEX) return AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor(Complex::sqrt2());
                    THROW_AUTOQ_ERROR("Unsupported mode!");
                } else {
                    if (mode == CONCRETE_COMPLEX) {
                        resultV = text;
                        encountered_term_undefined_error = true;
                        return Complex(0); // fake value only for continuing to execute
                    }
                    if (mode == SYMBOLIC_COMPLEX) {
                        return AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor(text, used_vars);
                    }
                    THROW_AUTOQ_ERROR("Unsupported mode!");
                }
            }
        } else {
            THROW_AUTOQ_ERROR("Unsupported complex grammar!");
        }
    }
