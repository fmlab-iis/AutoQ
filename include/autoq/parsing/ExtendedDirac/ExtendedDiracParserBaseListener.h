
// Generated from src/ExtendedDirac/ExtendedDiracParser.g4 by ANTLR 4.13.2

#pragma once


#include "antlr4-runtime.h"
#include "ExtendedDiracParserListener.h"


/**
 * This class provides an empty implementation of ExtendedDiracParserListener,
 * which can be extended to create a listener which only needs to handle a subset
 * of the available methods.
 */
class  ExtendedDiracParserBaseListener : public ExtendedDiracParserListener {
public:

  virtual void enterExpr(ExtendedDiracParser::ExprContext * /*ctx*/) override { }
  virtual void exitExpr(ExtendedDiracParser::ExprContext * /*ctx*/) override { }

  virtual void enterTset(ExtendedDiracParser::TsetContext * /*ctx*/) override { }
  virtual void exitTset(ExtendedDiracParser::TsetContext * /*ctx*/) override { }

  virtual void enterScset(ExtendedDiracParser::ScsetContext * /*ctx*/) override { }
  virtual void exitScset(ExtendedDiracParser::ScsetContext * /*ctx*/) override { }

  virtual void enterSet(ExtendedDiracParser::SetContext * /*ctx*/) override { }
  virtual void exitSet(ExtendedDiracParser::SetContext * /*ctx*/) override { }

  virtual void enterDiracs(ExtendedDiracParser::DiracsContext * /*ctx*/) override { }
  virtual void exitDiracs(ExtendedDiracParser::DiracsContext * /*ctx*/) override { }

  virtual void enterDirac(ExtendedDiracParser::DiracContext * /*ctx*/) override { }
  virtual void exitDirac(ExtendedDiracParser::DiracContext * /*ctx*/) override { }

  virtual void enterTerm(ExtendedDiracParser::TermContext * /*ctx*/) override { }
  virtual void exitTerm(ExtendedDiracParser::TermContext * /*ctx*/) override { }

  virtual void enterComplex(ExtendedDiracParser::ComplexContext * /*ctx*/) override { }
  virtual void exitComplex(ExtendedDiracParser::ComplexContext * /*ctx*/) override { }

  virtual void enterVarcons(ExtendedDiracParser::VarconsContext * /*ctx*/) override { }
  virtual void exitVarcons(ExtendedDiracParser::VarconsContext * /*ctx*/) override { }

  virtual void enterVarcon(ExtendedDiracParser::VarconContext * /*ctx*/) override { }
  virtual void exitVarcon(ExtendedDiracParser::VarconContext * /*ctx*/) override { }

  virtual void enterEq(ExtendedDiracParser::EqContext * /*ctx*/) override { }
  virtual void exitEq(ExtendedDiracParser::EqContext * /*ctx*/) override { }

  virtual void enterIneq(ExtendedDiracParser::IneqContext * /*ctx*/) override { }
  virtual void exitIneq(ExtendedDiracParser::IneqContext * /*ctx*/) override { }

  virtual void enterPredicate(ExtendedDiracParser::PredicateContext * /*ctx*/) override { }
  virtual void exitPredicate(ExtendedDiracParser::PredicateContext * /*ctx*/) override { }


  virtual void enterEveryRule(antlr4::ParserRuleContext * /*ctx*/) override { }
  virtual void exitEveryRule(antlr4::ParserRuleContext * /*ctx*/) override { }
  virtual void visitTerminal(antlr4::tree::TerminalNode * /*node*/) override { }
  virtual void visitErrorNode(antlr4::tree::ErrorNode * /*node*/) override { }

};

