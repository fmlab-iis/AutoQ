
// Generated from src/ExtendedDirac/ExtendedDiracParser.g4 by ANTLR 4.13.2

#pragma once


#include "antlr4-runtime.h"
#include "ExtendedDiracParser.h"



/**
 * This class defines an abstract visitor for a parse tree
 * produced by ExtendedDiracParser.
 */
class  ExtendedDiracParserVisitor : public antlr4::tree::AbstractParseTreeVisitor {
public:

  /**
   * Visit parse trees produced by ExtendedDiracParser.
   */
    virtual std::any visitExtendedDirac(ExtendedDiracParser::ExtendedDiracContext *context) = 0;

    virtual std::any visitSet(ExtendedDiracParser::SetContext *context) = 0;

    virtual std::any visitDiracs(ExtendedDiracParser::DiracsContext *context) = 0;

    virtual std::any visitDirac(ExtendedDiracParser::DiracContext *context) = 0;

    virtual std::any visitCket(ExtendedDiracParser::CketContext *context) = 0;

    virtual std::any visitComplex(ExtendedDiracParser::ComplexContext *context) = 0;

    virtual std::any visitAngle(ExtendedDiracParser::AngleContext *context) = 0;

    virtual std::any visitIjklens(ExtendedDiracParser::IjklensContext *context) = 0;

    virtual std::any visitIjklen(ExtendedDiracParser::IjklenContext *context) = 0;


};

