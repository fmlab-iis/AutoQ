#ifndef _AUTOQ_EXTENDED_DIRAC_PARSERS_HH_
#define _AUTOQ_EXTENDED_DIRAC_PARSERS_HH_
/** Extended Dirac parsers: ComplexParser, SymbolicComplexParser, ConstraintParser.
 *  Included from EvaluationVisitor.h inside the struct body.
 *  Uses .hh extension (no .inc.h). */
    class ComplexParser {
public:
    ComplexParser(const std::string &input, const std::map<std::string, Complex> &constMap = get_empty_const_map())
        : input_(input), index_(0), resultC(), resultV(), constMap_(constMap), unknownVariableErrorOccurred(false) {
        std::erase_if(input_, [](unsigned char ch) { return std::isspace(ch); });
        parse();
    }
    Complex getComplex() const {
        return resultC;
    }
    std::string getConstName() const {
        return resultV;
    }

private:
    std::string input_;
    size_t index_;
    Complex resultC;
    std::string resultV;
    const std::map<std::string, Complex> &constMap_;
    bool unknownVariableErrorOccurred;

    void parse() {
        EvaluationVisitor<AUTOQ::Symbol::Concrete> complexVisitor({constMap_}, {});
        complexVisitor.mode = EvaluationVisitor<AUTOQ::Symbol::Concrete>::CONCRETE_COMPLEX;
        auto visitResult = parse_extended_dirac_and_visit(input_, [](ExtendedDiracParser& p) { return static_cast<antlr4::tree::ParseTree*>(p.complex()); }, &complexVisitor);
        resultC = std::any_cast<AUTOQ::Complex::Complex>(visitResult);
        resultV = complexVisitor.resultV;
    }
};

class SymbolicComplexParser {
public:
    SymbolicComplexParser(const std::string &input, const std::map<std::string, Complex> &constMap = get_empty_const_map())
        : input_(input), index_(0), result(), constMap_(constMap), used_vars() {
        std::erase_if(input_, [](unsigned char ch) { return std::isspace(ch); });
        parse();
    }
    AUTOQ::Complex::SymbolicComplex getSymbolicComplex() const {
        return result;
    }
    std::set<std::string> getNewVars() const {
        return used_vars;
    }

private:
    std::string input_;
    size_t index_;
    AUTOQ::Complex::SymbolicComplex result;
    const std::map<std::string, Complex> &constMap_;
    std::set<std::string> used_vars;

    void parse() {
        EvaluationVisitor<AUTOQ::Symbol::Symbolic> complexVisitor({constMap_}, {});
        complexVisitor.mode = EvaluationVisitor<AUTOQ::Symbol::Symbolic>::SYMBOLIC_COMPLEX;
        auto visitResult = parse_extended_dirac_and_visit(input_, [](ExtendedDiracParser& p) { return static_cast<antlr4::tree::ParseTree*>(p.complex()); }, &complexVisitor);
        result = std::any_cast<AUTOQ::Complex::SymbolicComplex>(visitResult);
        used_vars = complexVisitor.used_vars;
    }
};

class ConstraintParser {
public:
    ConstraintParser(const std::string &input, const std::map<std::string, Complex> &constMap = get_empty_const_map())
        : input_(input), index_(0), result(), constMap_(constMap) {
        std::erase_if(input_, [](unsigned char ch) { return std::isspace(ch); });
        parse();
    }
    std::string getSMTexpression() const {
        return result;
    }

private:
    std::string input_;
    size_t index_;
    std::string result;
    const std::map<std::string, Complex> &constMap_;

    void parse() {
        EvaluationVisitor<AUTOQ::Symbol::Symbolic> predicateVisitor({constMap_}, {});
        predicateVisitor.mode = EvaluationVisitor<AUTOQ::Symbol::Symbolic>::SYMBOLIC_COMPLEX;
        auto visitResult = parse_extended_dirac_and_visit(input_, [](ExtendedDiracParser& p) { return static_cast<antlr4::tree::ParseTree*>(p.predicate()); }, &predicateVisitor);
        result = std::any_cast<z3::expr>(visitResult).to_string();
    }
};

#endif
