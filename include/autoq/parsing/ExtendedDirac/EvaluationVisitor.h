
#include "ExtendedDiracParserBaseVisitor.h"
#include "ExtendedDiracParser.h"

#include "autoq/aut_description.hh"
#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/complex/complex.hh"

template <typename Symbol>
class EvaluationVisitor : public ExtendedDiracParserBaseVisitor {
public:
    std::map<std::string, AUTOQ::Complex::Complex> constants;
    std::map<std::string, std::string> predicates;
    std::map<char, int> ijklens;
    EvaluationVisitor(const std::map<std::string, AUTOQ::Complex::Complex> &constants, const std::map<std::string, std::string> &predicates) : constants(constants), predicates(predicates), ijklens({}) {}

    std::any visitExtendedDirac(ExtendedDiracParser::ExtendedDiracContext *ctx) override {
        if (ctx->muloperators() != nullptr) { // RULE: accepted WHERE NEWLINES muloperators
            visit(ctx->muloperators()); // Notice that "mulmap" will be updated during the visit.
        }
        auto result = visit(ctx->accepted()); // RULE: accepted (WHERE NEWLINES muloperators)?
        if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Concrete>) {
            AUTOQ::Symbol::Concrete::mulmap.clear();
        } else if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Predicate>) {
            AUTOQ::Symbol::Predicate::mulmap.clear();
        } else { // if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Symbolic>) {
            // do nothing
        }
        return result;
    }

    std::any visitMuloperators(ExtendedDiracParser::MuloperatorsContext *ctx) override {
        for (const auto &e : ctx->muloperator()) {
            visit(e); // RULE: muloperator+
        }
        return {};
    }

    std::any visitMuloperator(ExtendedDiracParser::MuloperatorContext *ctx) override {
        if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Concrete>) {
            AUTOQ::Symbol::Concrete::mulmap[std::make_pair(ComplexParser(ctx->complex(0)->getText(), constants).getComplex(), ComplexParser(ctx->complex(1)->getText(), constants).getComplex())] = ComplexParser(ctx->complex(2)->getText(), constants).getComplex();
            // AUTOQ::Symbol::Concrete::mulmap[std::make_pair(ComplexParser(ctx->complex(1)->getText(), constants).getComplex(), ComplexParser(ctx->complex(0)->getText(), constants).getComplex())] = ComplexParser(ctx->complex(2)->getText(), constants).getComplex();
        } else if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Predicate>) {
            AUTOQ::Symbol::Predicate p[3];
            for (int i=0; i<3; i++) {
                auto str = ctx->complex(i)->getText();
                auto it = predicates.find(str);
                if (it == predicates.end())
                    p[i] = AUTOQ::Symbol::Predicate(str);
                else
                    p[i] = AUTOQ::Symbol::Predicate(it->second);
            }
            AUTOQ::Symbol::Predicate::mulmap[std::make_pair(p[0], p[1])] = p[2];
            // AUTOQ::Symbol::Predicate::mulmap[std::make_pair(p[1], p[0])] = p[2];
        } else if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Symbolic>) {
            AUTOQ::Symbol::Symbolic::mulmap[std::make_pair(AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(0)->getText(), constants).getSymbolicComplex()), AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(1)->getText(), constants).getSymbolicComplex()))] = AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(2)->getText(), constants).getSymbolicComplex());
            // AUTOQ::Symbol::Symbolic::mulmap[std::make_pair(AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(1)->getText(), constants).getSymbolicComplex()), AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(0)->getText(), constants).getSymbolicComplex()))] = AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(2)->getText(), constants).getSymbolicComplex());
        } else {
            THROW_AUTOQ_ERROR("This kind of symbol is still unsupported!");
        }
        return {};
    }

    std::any visitAccepted(ExtendedDiracParser::AcceptedContext *ctx) override {
        if (ctx->set().size() == 1) { // RULE: set
            return visit(ctx->set(0));
        } else { // RULE: set '\\' set
            // TODO:
            /*
            auto left = visit(ctx->set(0)); // Left operand
            auto right = visit(ctx->set(1)); // Right operand
            return visit(ctx->set(0)); //std::make_pair(left, right);
            */
           return {};
        }
    }

    std::any visitSet(ExtendedDiracParser::SetContext *ctx) override {
        if (ctx->n != nullptr) { // RULE: set '^' n
            int times = std::stoi(ctx->n->getText());
            if (times == 1) {
                return visit(ctx->set(0));
            } else { // if (times > 1) {
                auto lsta = std::any_cast<AUTOQ::Automata<Symbol>>(visit(ctx->set(0)));
                auto result = lsta;
                while ((--times) > 0) {
                    result = result * lsta; // TODO: implement *=
                }
                return result;
            }
        } else if (ctx->op == nullptr) {
            if (!ctx->set().empty()) { // RULE: '(' set ')'
                return visit(ctx->set(0));
            } else if (ctx->diracs() != nullptr) { // RULE: '{' diracs '}'
                return visit(ctx->diracs());
            } else { // if (ctx->dirac() != nullptr && ctx->ijklens() != nullptr) { // RULE: '{' dirac '|' ijklens '}'
                ijklens = std::any_cast<std::map<char, int>>(visit(ctx->ijklens()));
                return visit(ctx->dirac());
            }
        } else if (ctx->op->getType() == ExtendedDiracParser::PROD) { // RULE: set op=PROD set
            return std::any_cast<AUTOQ::Automata<Symbol>>(visit(ctx->set(0))) * std::any_cast<AUTOQ::Automata<Symbol>>(visit(ctx->set(1)));
        } else if (ctx->op->getType() == ExtendedDiracParser::UNION) { // RULE: set op=UNION set
            return std::any_cast<AUTOQ::Automata<Symbol>>(visit(ctx->set(0))) || std::any_cast<AUTOQ::Automata<Symbol>>(visit(ctx->set(1)));
        } else { // if (ctx->op->getType() == ExtendedDiracParser::INTERSECTION) { // RULE: set op=INTERSECTION set
            // TODO: implement &&
            /**/
            return {};
        }
    }

    std::any visitDiracs(ExtendedDiracParser::DiracsContext *ctx) override {
        if (ctx->diracs() == nullptr) { // RULE: dirac
            return visit(ctx->dirac());
        } else { // RULE: diracs ',' dirac
            return std::any_cast<AUTOQ::Automata<Symbol>>(visit(ctx->diracs())) || std::any_cast<AUTOQ::Automata<Symbol>>(visit(ctx->dirac()));
        }
    }

    std::any visitDirac(ExtendedDiracParser::DiracContext *ctx) override {
        return from_tree_to_automaton<Symbol>(ctx->getText(), constants, predicates, ijklens);
    }

    std::any visitIjklens(ExtendedDiracParser::IjklensContext *ctx) override {
        if (ctx->ijklens() == nullptr) { // RULE: ijklen
            return visit(ctx->ijklen());
        } else { // RULE: ijklens ',' ijklen
            auto result = std::any_cast<std::map<char, int>>(visit(ctx->ijklens())); // previous
            auto present = std::any_cast<std::map<char, int>>(visit(ctx->ijklen()));
            if (result.find(present.begin()->first) == result.end()) {
                result[present.begin()->first] = present.begin()->second;
            } else {
                THROW_AUTOQ_ERROR("The same index is used more than once!");
            }
            return result;
        }
    }

    std::any visitIjklen(ExtendedDiracParser::IjklenContext *ctx) override {
        std::string var = ctx->var->getText(); // RULE: BAR var=NAME BAR EQ len=DIGITS
        if (var.length() == 1) {
            int len = std::stoi(ctx->len->getText());
            return std::map<char, int>{{var[0], len}};
        } else {
            THROW_AUTOQ_ERROR("The index must be a single character!");
        }
    }
};
