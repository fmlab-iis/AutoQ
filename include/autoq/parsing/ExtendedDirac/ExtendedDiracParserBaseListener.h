
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

  virtual void enterExtendedDirac(ExtendedDiracParser::ExtendedDiracContext * /*ctx*/) override { }
  virtual void exitExtendedDirac(ExtendedDiracParser::ExtendedDiracContext * /*ctx*/) override { }

  virtual void enterSet(ExtendedDiracParser::SetContext * /*ctx*/) override { }
  virtual void exitSet(ExtendedDiracParser::SetContext * /*ctx*/) override { }

  virtual void enterDiracs(ExtendedDiracParser::DiracsContext * /*ctx*/) override { }
  virtual void exitDiracs(ExtendedDiracParser::DiracsContext * /*ctx*/) override { }

  virtual void enterDirac(ExtendedDiracParser::DiracContext * /*ctx*/) override { }
  virtual void exitDirac(ExtendedDiracParser::DiracContext * /*ctx*/) override { }

  virtual void enterCket(ExtendedDiracParser::CketContext * /*ctx*/) override { }
  virtual void exitCket(ExtendedDiracParser::CketContext * /*ctx*/) override { }

  virtual void enterComplex(ExtendedDiracParser::ComplexContext * /*ctx*/) override { }
  virtual void exitComplex(ExtendedDiracParser::ComplexContext * /*ctx*/) override { }

  virtual void enterAngle(ExtendedDiracParser::AngleContext * /*ctx*/) override { }
  virtual void exitAngle(ExtendedDiracParser::AngleContext * /*ctx*/) override { }

  virtual void enterIjklens(ExtendedDiracParser::IjklensContext * /*ctx*/) override { }
  virtual void exitIjklens(ExtendedDiracParser::IjklensContext * /*ctx*/) override { }

  virtual void enterIjklen(ExtendedDiracParser::IjklenContext * /*ctx*/) override { }
  virtual void exitIjklen(ExtendedDiracParser::IjklenContext * /*ctx*/) override { }


  virtual void enterEveryRule(antlr4::ParserRuleContext * /*ctx*/) override { }
  virtual void exitEveryRule(antlr4::ParserRuleContext * /*ctx*/) override { }
  virtual void visitTerminal(antlr4::tree::TerminalNode * /*node*/) override { }
  virtual void visitErrorNode(antlr4::tree::ErrorNode * /*node*/) override { }

};

