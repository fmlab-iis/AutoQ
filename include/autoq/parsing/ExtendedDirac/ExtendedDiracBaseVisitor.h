
// Generated from src/ExtendedDirac/ExtendedDirac.g4 by ANTLR 4.13.2

#pragma once


#include "antlr4-runtime.h"
#include "ExtendedDiracVisitor.h"


/**
 * This class provides an empty implementation of ExtendedDiracVisitor, which can be
 * extended to create a visitor which only needs to handle a subset of the available methods.
 */
class  ExtendedDiracBaseVisitor : public ExtendedDiracVisitor {
public:

  virtual std::any visitExtendedDirac(ExtendedDiracParser::ExtendedDiracContext *ctx) override {
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

