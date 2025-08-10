
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
    virtual std::any visitExpr(ExtendedDiracParser::ExprContext *context) = 0;

    virtual std::any visitTset(ExtendedDiracParser::TsetContext *context) = 0;

    virtual std::any visitScset(ExtendedDiracParser::ScsetContext *context) = 0;

    virtual std::any visitSet(ExtendedDiracParser::SetContext *context) = 0;

    virtual std::any visitDiracs(ExtendedDiracParser::DiracsContext *context) = 0;

    virtual std::any visitDirac(ExtendedDiracParser::DiracContext *context) = 0;

    virtual std::any visitTerm(ExtendedDiracParser::TermContext *context) = 0;

    virtual std::any visitVarcons(ExtendedDiracParser::VarconsContext *context) = 0;

    virtual std::any visitVarcon(ExtendedDiracParser::VarconContext *context) = 0;

    virtual std::any visitIneq(ExtendedDiracParser::IneqContext *context) = 0;


};

