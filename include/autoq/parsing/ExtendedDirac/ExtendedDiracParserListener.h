
// Generated from src/ExtendedDirac/ExtendedDiracParser.g4 by ANTLR 4.13.2

#pragma once


#include "antlr4-runtime.h"
#include "ExtendedDiracParser.h"


/**
 * This interface defines an abstract listener for a parse tree produced by ExtendedDiracParser.
 */
class  ExtendedDiracParserListener : public antlr4::tree::ParseTreeListener {
public:

  virtual void enterExtendedDirac(ExtendedDiracParser::ExtendedDiracContext *ctx) = 0;
  virtual void exitExtendedDirac(ExtendedDiracParser::ExtendedDiracContext *ctx) = 0;

  virtual void enterSet(ExtendedDiracParser::SetContext *ctx) = 0;
  virtual void exitSet(ExtendedDiracParser::SetContext *ctx) = 0;

  virtual void enterDiracs(ExtendedDiracParser::DiracsContext *ctx) = 0;
  virtual void exitDiracs(ExtendedDiracParser::DiracsContext *ctx) = 0;

  virtual void enterDirac(ExtendedDiracParser::DiracContext *ctx) = 0;
  virtual void exitDirac(ExtendedDiracParser::DiracContext *ctx) = 0;

  virtual void enterCket(ExtendedDiracParser::CketContext *ctx) = 0;
  virtual void exitCket(ExtendedDiracParser::CketContext *ctx) = 0;

  virtual void enterComplex(ExtendedDiracParser::ComplexContext *ctx) = 0;
  virtual void exitComplex(ExtendedDiracParser::ComplexContext *ctx) = 0;

  virtual void enterAngle(ExtendedDiracParser::AngleContext *ctx) = 0;
  virtual void exitAngle(ExtendedDiracParser::AngleContext *ctx) = 0;

  virtual void enterIjklens(ExtendedDiracParser::IjklensContext *ctx) = 0;
  virtual void exitIjklens(ExtendedDiracParser::IjklensContext *ctx) = 0;

  virtual void enterIjklen(ExtendedDiracParser::IjklenContext *ctx) = 0;
  virtual void exitIjklen(ExtendedDiracParser::IjklenContext *ctx) = 0;


};

