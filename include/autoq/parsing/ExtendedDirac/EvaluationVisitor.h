
#include "ExtendedDiracParserBaseVisitor.h"
#include "ExtendedDiracParser.h"

#include "autoq/aut_description.hh"
#include "autoq/symbol/concrete.hh"
#include "autoq/complex/complex.hh"

// Thanks to https://github.com/boostorg/multiprecision/issues/297
boost::multiprecision::cpp_int bin_2_dec2(const std::string_view& num)
{
    boost::multiprecision::cpp_int dec_value = 0;
    auto cptr = num.data();
    long long len  = num.size();
    // check if big enough to have 0b postfix
    if (num.size() > 2) {
        // check if 2nd character is the 'b' binary postfix
        // skip over it & adjust length accordingly if it is
        if (num[1] == 'b' || num[1] == 'B') {
            cptr += 2;
            len  -= 2;
        }
    }
    // change i's type to cpp_int if the number of digits is greater
    // than std::numeric_limits<size_t>::max()
    for (long long i = len - 1; 0 <= i; ++cptr, --i) {
        if (*cptr == '1') {
            boost::multiprecision::bit_set(/*.val = */ dec_value, /*.pos = */ i);
        }
    }
    return dec_value;
}

template <typename Symbol>
class EvaluationVisitor : public ExtendedDiracParserBaseVisitor {
public:
    std::map<std::string, AUTOQ::Complex::Complex> constants;
    std::map<std::string, std::string> predicates;
    EvaluationVisitor(const std::map<std::string, AUTOQ::Complex::Complex> &constants, const std::map<std::string, std::string> &predicates) : constants(constants), predicates(predicates) {}

    std::any visitExtendedDirac(ExtendedDiracParser::ExtendedDiracContext *ctx) override {
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
                // TODO
                /**/
                return {};
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
        return from_tree_to_automaton<Symbol>(ctx->getText(), constants, predicates);
    }

    // std::any visitIjklens(ExtendedDiracParser::IjklensContext *ctx) override {
    //     return visitChildren(ctx);
    // }

    // std::any visitIjklen(ExtendedDiracParser::IjklenContext *ctx) override {
    //     return visitChildren(ctx);
    // }
};
