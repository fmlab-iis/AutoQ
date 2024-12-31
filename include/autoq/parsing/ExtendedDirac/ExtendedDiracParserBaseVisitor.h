
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

  virtual std::any visitExtendedDirac(ExtendedDiracParser::ExtendedDiracContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitMuloperators(ExtendedDiracParser::MuloperatorsContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitMuloperator(ExtendedDiracParser::MuloperatorContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitAccepted(ExtendedDiracParser::AcceptedContext *ctx) override {
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

  virtual std::any visitCket(ExtendedDiracParser::CketContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitComplex(ExtendedDiracParser::ComplexContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitAngle(ExtendedDiracParser::AngleContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitIjklens(ExtendedDiracParser::IjklensContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual std::any visitIjklen(ExtendedDiracParser::IjklenContext *ctx) override {
    return visitChildren(ctx);
  }


};

