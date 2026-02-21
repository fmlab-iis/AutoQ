#ifndef _AUTOQ_EVALUATION_VISITOR_HH_
#define _AUTOQ_EVALUATION_VISITOR_HH_

#include "ExtendedDiracParsingCommon.h"

#include "autoq/aut_description.hh"
#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/complex/complex.hh"
#include "autoq/complex/symbolic_complex.hh"
#include "autoq/complex/constrained_complex.hh"
#include "z3/z3++.h"

#include <queue>

template <typename Symbol = AUTOQ::Symbol::Concrete, typename Symbol2 = Symbol>
struct EvaluationVisitor : public ExtendedDiracParserBaseVisitor {
    using Complex = AUTOQ::Complex::Complex;
#include "ExtendedDiracParsers.hh"

    typedef std::pair<int, int> unitsplit_t;
    typedef std::vector<unitsplit_t> strsplit_t;
    typedef std::vector<strsplit_t> strs2split_t;
    typedef std::vector<strs2split_t> segment2strs_t;
    typedef std::vector<std::vector<unitsplit_t>> segment2split_t;
    typedef std::vector<unitsplit_t> currentSplit_t;
    typedef std::pair<int, int> edge_t; // unordered: using std::minmax
    typedef std::set<edge_t> graph_t;
    typedef std::vector<int> cc_t;
    typedef std::set<cc_t> perm_t;
    typedef std::vector<perm_t> segment2perm_t;
    typedef std::pair<char, std::string> eq_t;
    typedef std::map<char, std::string> eqs_t;
    typedef std::pair<std::string, std::string> ineq_t; // unordered: using std::minmax, notice that we do not use char here because there may be some binary strings as constants in future use.
    typedef std::set<ineq_t> ineqS_t;
    typedef std::set<char> vars_t;
    typedef std::vector<vars_t> unit2vars_t;
    typedef std::pair<unit2vars_t, ineqS_t> relation_t;
    typedef std::pair<std::set<char>, std::string> varcon_t; // ordered
    typedef std::vector<varcon_t> varconS_t;

    enum mode_t {EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT,
                 SPLIT_TENSORED_EXPRESSION_INTO_VECTOR_OF_SETS_WITHOUT_TENSOR, // new!!!
                 COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES, // may input with ;
                 REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT, // may input with ;
                 COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION, // may input with ;
                 REORDER_UNITS_BY_THE_GROUP, // may input with ;
                 EVALUATE_EACH_SET_BRACES_TO_LSTA,
                 SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS, // a submode in EVALUATE_EACH_SET_BRACES_TO_LSTA
                 SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY, // a submode in EVALUATE_EACH_SET_BRACES_TO_LSTA

                 CONCRETE_COMPLEX,
                 SYMBOLIC_COMPLEX,
                };
    mode_t mode; // by default, the first one

    std::map<char, int> globalVar2len; // record all control variables used in {diracs : varcons}
    std::set<char> usedVars; // record all variables currently used in {diracs : varcons} for preventing naming collision.
    segment2split_t segment2split;
    currentSplit_t currentSplit;
    segment2perm_t segment2perm;
    perm_t currentPerm;
    std::vector<size_t> remember_the_lengths_of_each_unit_position;
    bool switch_symbol_to_second;
    bool do_not_throw_term_undefined_error;
    bool encountered_term_undefined_error;
    std::set<std::string> used_vars;
    std::string resultV; // variable
    z3::context z3Ctx;

    std::map<std::string, AUTOQ::Complex::Complex> constants;
    std::vector<std::map<std::string, AUTOQ::Complex::Complex>> constantsVector;
    std::string predicateConstraints;
    std::vector<std::string> predicateConstraintsVector;
    EvaluationVisitor(const std::vector<std::map<std::string, AUTOQ::Complex::Complex>> &constantsVector, const std::vector<std::string> &predicateConstraintsVector) :
        mode(EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT),
        globalVar2len(),
        usedVars(),
        segment2split(),
        currentSplit(),
        segment2perm(),
        currentPerm(),
        remember_the_lengths_of_each_unit_position(),
        switch_symbol_to_second(false),
        do_not_throw_term_undefined_error(false),
        encountered_term_undefined_error(false),
        used_vars(),
        resultV(),
        z3Ctx(),
        constants(constantsVector.empty() ? std::map<std::string, AUTOQ::Complex::Complex>() : constantsVector.at(0)),
        constantsVector(constantsVector),
        predicateConstraints(predicateConstraintsVector.empty() ? "" : predicateConstraintsVector.at(0)),
        predicateConstraintsVector(predicateConstraintsVector) {}
    std::any let_visitor_parse_string(const std::string &input) {
        return parse_extended_dirac_and_visit(input, [](ExtendedDiracParser& p) { return static_cast<antlr4::tree::ParseTree*>(p.expr()); }, this);
    }

    /* -------- VisitExpr: expression (expr → tset → scset → set) -------- */
    // std::any visitExtendedDirac(ExtendedDiracParser::ExtendedDiracContext *ctx) override {
    //     if (ctx->muloperators() != nullptr) { // RULE: accepted WHERE NEWLINES muloperators
    //         visit(ctx->muloperators()); // Notice that "mulmap" will be updated during the visit.
    //     }
    //     auto result = visit(ctx->accepted()); // RULE: accepted (WHERE NEWLINES muloperators)?
    //     if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Concrete>) {
    //         AUTOQ::Symbol::Concrete::mulmap.clear();
    //     } else if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Predicate>) {
    //         AUTOQ::Symbol::Predicate::mulmap.clear();
    //     } else { // if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Symbolic>) {
    //         // do nothing
    //     }
    //     return result;
    // }

    // std::any visitMuloperators(ExtendedDiracParser::MuloperatorsContext *ctx) override {
    //     for (const auto &e : ctx->muloperator()) {
    //         visit(e); // RULE: muloperator+
    //     }
    //     return {};
    // }

    // std::any visitMuloperator(ExtendedDiracParser::MuloperatorContext *ctx) override {
    //     if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Concrete>) {
    //         AUTOQ::Symbol::Concrete::mulmap[std::make_pair(ComplexParser(ctx->complex(0)->getText(), constants).getComplex(), ComplexParser(ctx->complex(1)->getText(), constants).getComplex())] = ComplexParser(ctx->complex(2)->getText(), constants).getComplex();
    //         // AUTOQ::Symbol::Concrete::mulmap[std::make_pair(ComplexParser(ctx->complex(1)->getText(), constants).getComplex(), ComplexParser(ctx->complex(0)->getText(), constants).getComplex())] = ComplexParser(ctx->complex(2)->getText(), constants).getComplex();
    //     } else if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Predicate>) {
    //         AUTOQ::Symbol::Predicate p[3];
    //         for (int i=0; i<3; i++) {
    //             auto str = ctx->complex(i)->getText();
    //             auto it = predicates.find(str);
    //             if (it == predicates.end())
    //                 p[i] = AUTOQ::Symbol::Predicate(str);
    //             else
    //                 p[i] = AUTOQ::Symbol::Predicate(it->second);
    //         }
    //         AUTOQ::Symbol::Predicate::mulmap[std::make_pair(p[0], p[1])] = p[2];
    //         // AUTOQ::Symbol::Predicate::mulmap[std::make_pair(p[1], p[0])] = p[2];
    //     } else if constexpr(std::is_same_v<Symbol, AUTOQ::Symbol::Symbolic>) {
    //         AUTOQ::Symbol::Symbolic::mulmap[std::make_pair(AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(0)->getText(), constants).getSymbolicComplex()), AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(1)->getText(), constants).getSymbolicComplex()))] = AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(2)->getText(), constants).getSymbolicComplex());
    //         // AUTOQ::Symbol::Symbolic::mulmap[std::make_pair(AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(1)->getText(), constants).getSymbolicComplex()), AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(0)->getText(), constants).getSymbolicComplex()))] = AUTOQ::Symbol::Symbolic(AUTOQ::Parsing::SymbolicComplexParser(ctx->complex(2)->getText(), constants).getSymbolicComplex());
    //     } else {
    //         THROW_AUTOQ_ERROR("This kind of symbol is still unsupported!");
    //     }
    //     return {};
    // }

    // std::any visitAccepted(ExtendedDiracParser::AcceptedContext *ctx) override {
    //     if (ctx->set().size() == 1) { // RULE: set
    //         return visit(ctx->set(0));
    //     } else { // RULE: set '\\' set
    //         // TODO:
    //         /*
    //         auto left = visit(ctx->set(0)); // Left operand
    //         auto right = visit(ctx->set(1)); // Right operand
    //         return visit(ctx->set(0)); //std::make_pair(left, right);
    //         */
    //        return {};
    //     }
    // }

#include "EvaluationVisitorExpr.h"
#include "EvaluationVisitorHelpers.h"
#include "EvaluationVisitorTset.h"
#include "EvaluationVisitorScset.h"
#include "EvaluationVisitorSet.h"

#include "EvaluationVisitorDirac.h"
#include "EvaluationVisitorVarcons.h"

#include "EvaluationVisitorComplex.h"

    // std::any visitAngle(ExtendedDiracParser::AngleContext *ctx) override {
    //     if (ctx->n != nullptr) {
    //         return 0; // ei2pi(2*pi*n) = ei2pi(0)
    //     } else if (ctx->SUB() == nullptr) {
    //         return boost::rational<boost::multiprecision::cpp_int>(std::stoi(ctx->x->getText()), std::stoi(ctx->y->getText()));
    //     } else {
    //         return boost::rational<boost::multiprecision::cpp_int>(-std::stoi(ctx->x->getText()), std::stoi(ctx->y->getText()));
    //     }
    // }

#include "EvaluationVisitorPredicate.h"
};

#endif
