
// Generated from src/ExtendedDirac/ExtendedDiracParser.g4 by ANTLR 4.13.2

#pragma once


#include "antlr4-runtime.h"
#include "ExtendedDiracParser.h"


/**
 * This interface defines an abstract listener for a parse tree produced by ExtendedDiracParser.
 */
class  ExtendedDiracParserListener : public antlr4::tree::ParseTreeListener {
public:

  virtual void enterExpr(ExtendedDiracParser::ExprContext *ctx) = 0;
  virtual void exitExpr(ExtendedDiracParser::ExprContext *ctx) = 0;

  virtual void enterTset(ExtendedDiracParser::TsetContext *ctx) = 0;
  virtual void exitTset(ExtendedDiracParser::TsetContext *ctx) = 0;

  virtual void enterScset(ExtendedDiracParser::ScsetContext *ctx) = 0;
  virtual void exitScset(ExtendedDiracParser::ScsetContext *ctx) = 0;

  virtual void enterSet(ExtendedDiracParser::SetContext *ctx) = 0;
  virtual void exitSet(ExtendedDiracParser::SetContext *ctx) = 0;

  virtual void enterDiracs(ExtendedDiracParser::DiracsContext *ctx) = 0;
  virtual void exitDiracs(ExtendedDiracParser::DiracsContext *ctx) = 0;

  virtual void enterDirac(ExtendedDiracParser::DiracContext *ctx) = 0;
  virtual void exitDirac(ExtendedDiracParser::DiracContext *ctx) = 0;

  virtual void enterTerm(ExtendedDiracParser::TermContext *ctx) = 0;
  virtual void exitTerm(ExtendedDiracParser::TermContext *ctx) = 0;

  virtual void enterComplex(ExtendedDiracParser::ComplexContext *ctx) = 0;
  virtual void exitComplex(ExtendedDiracParser::ComplexContext *ctx) = 0;

  virtual void enterAngle(ExtendedDiracParser::AngleContext *ctx) = 0;
  virtual void exitAngle(ExtendedDiracParser::AngleContext *ctx) = 0;

  virtual void enterVarcons(ExtendedDiracParser::VarconsContext *ctx) = 0;
  virtual void exitVarcons(ExtendedDiracParser::VarconsContext *ctx) = 0;

  virtual void enterVarcon(ExtendedDiracParser::VarconContext *ctx) = 0;
  virtual void exitVarcon(ExtendedDiracParser::VarconContext *ctx) = 0;

  virtual void enterEq(ExtendedDiracParser::EqContext *ctx) = 0;
  virtual void exitEq(ExtendedDiracParser::EqContext *ctx) = 0;

  virtual void enterIneq(ExtendedDiracParser::IneqContext *ctx) = 0;
  virtual void exitIneq(ExtendedDiracParser::IneqContext *ctx) = 0;

  virtual void enterPredicate(ExtendedDiracParser::PredicateContext *ctx) = 0;
  virtual void exitPredicate(ExtendedDiracParser::PredicateContext *ctx) = 0;


};

