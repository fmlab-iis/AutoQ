
// Generated from src/ExtendedDirac/ExtendedDiracParser.g4 by ANTLR 4.13.2

#pragma once


#include "antlr4-runtime.h"
#include "ExtendedDiracParserVisitor.h"


/**
 * This class provides an empty implementation of ExtendedDiracParserVisitor, which can be
 * extended to create a visitor which only needs to handle a subset of the available methods.
 */
class  ExtendedDiracParserBaseVisitor : public ExtendedDiracParserVisitor {
public:

  virtual std::any visitExpr(ExtendedDiracParser::ExprContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitTset(ExtendedDiracParser::TsetContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitScset(ExtendedDiracParser::ScsetContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitSet(ExtendedDiracParser::SetContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitDiracs(ExtendedDiracParser::DiracsContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitDirac(ExtendedDiracParser::DiracContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitTerm(ExtendedDiracParser::TermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitComplex(ExtendedDiracParser::ComplexContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitAngle(ExtendedDiracParser::AngleContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitVarcons(ExtendedDiracParser::VarconsContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitVarcon(ExtendedDiracParser::VarconContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitEq(ExtendedDiracParser::EqContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitIneq(ExtendedDiracParser::IneqContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitPredicate(ExtendedDiracParser::PredicateContext *ctx) override {
    return visitChildren(ctx);
  }


};

