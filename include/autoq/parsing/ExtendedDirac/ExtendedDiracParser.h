
// Generated from src/ExtendedDirac/ExtendedDiracParser.g4 by ANTLR 4.13.2

#pragma once


#include "antlr4-runtime.h"




class  ExtendedDiracParser : public antlr4::Parser {
public:
  enum {
    ADD = 1, BAR = 2, COMMA = 3, COLON = 4, DIV = 5, EQ = 6, LEFT_PARENTHESIS = 7, 
    LEFT_BRACE = 8, MUL = 9, NE = 10, NEWLINES = 11, POWER = 12, PRIME = 13, 
    PROD = 14, RIGHT_ANGLE_BRACKET = 15, RIGHT_PARENTHESIS = 16, RIGHT_BRACE = 17, 
    SEMICOLON = 18, SETMINUS = 19, STR = 20, SUB = 21, SUM = 22, UNION = 23, 
    WS = 24, LOGICAL_AND = 25, LOGICAL_OR = 26, LOGICAL_NOT = 27, LESS_THAN = 28, 
    LESS_EQUAL = 29, GREATER_EQUAL = 30
  };

  enum {
    RuleExpr = 0, RuleTset = 1, RuleScset = 2, RuleSet = 3, RuleDiracs = 4, 
    RuleDirac = 5, RuleTerm = 6, RuleComplex = 7, RuleVarcons = 8, RuleVarcon = 9, 
    RuleEq = 10, RuleIneq = 11, RulePredicate = 12
  };

  explicit ExtendedDiracParser(antlr4::TokenStream *input);

  ExtendedDiracParser(antlr4::TokenStream *input, const antlr4::atn::ParserATNSimulatorOptions &options);

  ~ExtendedDiracParser() override;

  std::string getGrammarFileName() const override;

  const antlr4::atn::ATN& getATN() const override;

  const std::vector<std::string>& getRuleNames() const override;

  const antlr4::dfa::Vocabulary& getVocabulary() const override;

  antlr4::atn::SerializedATNView getSerializedATN() const override;


      bool isSymbolicAutomaton = false;
      std::set<std::string> predefinedConstants;

      bool areAllDigits(const std::string& text) {
          return std::all_of(text.begin(), text.end(), [](char c) { return '0' <= c && c <= '9'; });
      }
      bool isNonZero(const std::string& text) {
          return areAllDigits(text) && std::stoi(text) != 0;
      }
      bool isALowercaseLetter(const std::string& text) {
          return text.length() == 1 && 'a' <= text.at(0) && text.at(0) <= 'z';
      }
      bool isAConstantBinaryString(const std::string& text) {
          return std::all_of(text.begin(), text.end(), [](char c) { return c == '0' || c == '1'; });
      }


  class ExprContext;
  class TsetContext;
  class ScsetContext;
  class SetContext;
  class DiracsContext;
  class DiracContext;
  class TermContext;
  class ComplexContext;
  class VarconsContext;
  class VarconContext;
  class EqContext;
  class IneqContext;
  class PredicateContext; 

  class  ExprContext : public antlr4::ParserRuleContext {
  public:
    ExprContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<TsetContext *> tset();
    TsetContext* tset(size_t i);
    antlr4::tree::TerminalNode *EOF();
    antlr4::tree::TerminalNode *SETMINUS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  ExprContext* expr();

  class  TsetContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *N = nullptr;
    TsetContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ScsetContext *scset();
    SetContext *set();
    antlr4::tree::TerminalNode *POWER();
    antlr4::tree::TerminalNode *STR();
    std::vector<TsetContext *> tset();
    TsetContext* tset(size_t i);
    antlr4::tree::TerminalNode *MUL();
    antlr4::tree::TerminalNode *PROD();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  TsetContext* tset();
  TsetContext* tset(int precedence);
  class  ScsetContext : public antlr4::ParserRuleContext {
  public:
    ScsetContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    SetContext *set();
    ScsetContext *scset();
    antlr4::tree::TerminalNode *SEMICOLON();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  ScsetContext* scset();
  ScsetContext* scset(int precedence);
  class  SetContext : public antlr4::ParserRuleContext {
  public:
    SetContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LEFT_BRACE();
    DiracsContext *diracs();
    antlr4::tree::TerminalNode *RIGHT_BRACE();
    antlr4::tree::TerminalNode *COLON();
    VarconsContext *varcons();
    std::vector<SetContext *> set();
    SetContext* set(size_t i);
    antlr4::tree::TerminalNode *UNION();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  SetContext* set();
  SetContext* set(int precedence);
  class  DiracsContext : public antlr4::ParserRuleContext {
  public:
    DiracsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    DiracContext *dirac();
    DiracsContext *diracs();
    antlr4::tree::TerminalNode *COMMA();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  DiracsContext* diracs();
  DiracsContext* diracs(int precedence);
  class  DiracContext : public antlr4::ParserRuleContext {
  public:
    DiracContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    TermContext *term();
    DiracContext *dirac();
    antlr4::tree::TerminalNode *ADD();
    antlr4::tree::TerminalNode *SUB();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  DiracContext* dirac();
  DiracContext* dirac(int precedence);
  class  TermContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *VStr = nullptr;
    TermContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *BAR();
    antlr4::tree::TerminalNode *RIGHT_ANGLE_BRACKET();
    antlr4::tree::TerminalNode *STR();
    ComplexContext *complex();
    antlr4::tree::TerminalNode *SUM();
    VarconsContext *varcons();
    antlr4::tree::TerminalNode *SUB();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  TermContext* term();

  class  ComplexContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *sub = nullptr;
    antlr4::Token *func = nullptr;
    antlr4::Token *var = nullptr;
    antlr4::Token *op = nullptr;
    antlr4::Token *n = nullptr;
    ComplexContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ComplexContext *> complex();
    ComplexContext* complex(size_t i);
    antlr4::tree::TerminalNode *SUB();
    antlr4::tree::TerminalNode *LEFT_PARENTHESIS();
    antlr4::tree::TerminalNode *RIGHT_PARENTHESIS();
    antlr4::tree::TerminalNode *STR();
    antlr4::tree::TerminalNode *MUL();
    antlr4::tree::TerminalNode *DIV();
    antlr4::tree::TerminalNode *ADD();
    antlr4::tree::TerminalNode *POWER();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  ComplexContext* complex();
  ComplexContext* complex(int precedence);
  class  VarconsContext : public antlr4::ParserRuleContext {
  public:
    VarconsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    VarconContext *varcon();
    VarconsContext *varcons();
    antlr4::tree::TerminalNode *COMMA();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  VarconsContext* varcons();
  VarconsContext* varcons(int precedence);
  class  VarconContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *V = nullptr;
    antlr4::Token *N = nullptr;
    VarconContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> BAR();
    antlr4::tree::TerminalNode* BAR(size_t i);
    antlr4::tree::TerminalNode *EQ();
    std::vector<antlr4::tree::TerminalNode *> STR();
    antlr4::tree::TerminalNode* STR(size_t i);
    EqContext *eq();
    IneqContext *ineq();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  VarconContext* varcon();

  class  EqContext : public antlr4::ParserRuleContext {
  public:
    EqContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ComplexContext *> complex();
    ComplexContext* complex(size_t i);
    antlr4::tree::TerminalNode *EQ();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  EqContext* eq();

  class  IneqContext : public antlr4::ParserRuleContext {
  public:
    IneqContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ComplexContext *> complex();
    ComplexContext* complex(size_t i);
    antlr4::tree::TerminalNode *NE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  IneqContext* ineq();

  class  PredicateContext : public antlr4::ParserRuleContext {
  public:
    PredicateContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    EqContext *eq();
    IneqContext *ineq();
    std::vector<ComplexContext *> complex();
    ComplexContext* complex(size_t i);
    antlr4::tree::TerminalNode *LESS_THAN();
    antlr4::tree::TerminalNode *LESS_EQUAL();
    antlr4::tree::TerminalNode *RIGHT_ANGLE_BRACKET();
    antlr4::tree::TerminalNode *GREATER_EQUAL();
    antlr4::tree::TerminalNode *LOGICAL_NOT();
    std::vector<PredicateContext *> predicate();
    PredicateContext* predicate(size_t i);
    antlr4::tree::TerminalNode *LEFT_PARENTHESIS();
    antlr4::tree::TerminalNode *RIGHT_PARENTHESIS();
    antlr4::tree::TerminalNode *LOGICAL_AND();
    antlr4::tree::TerminalNode *LOGICAL_OR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  PredicateContext* predicate();
  PredicateContext* predicate(int precedence);

  bool sempred(antlr4::RuleContext *_localctx, size_t ruleIndex, size_t predicateIndex) override;

  bool tsetSempred(TsetContext *_localctx, size_t predicateIndex);
  bool scsetSempred(ScsetContext *_localctx, size_t predicateIndex);
  bool setSempred(SetContext *_localctx, size_t predicateIndex);
  bool diracsSempred(DiracsContext *_localctx, size_t predicateIndex);
  bool diracSempred(DiracContext *_localctx, size_t predicateIndex);
  bool complexSempred(ComplexContext *_localctx, size_t predicateIndex);
  bool varconsSempred(VarconsContext *_localctx, size_t predicateIndex);
  bool varconSempred(VarconContext *_localctx, size_t predicateIndex);
  bool predicateSempred(PredicateContext *_localctx, size_t predicateIndex);

  // By default the static state used to implement the parser is lazily initialized during the first
  // call to the constructor. You can call this function if you wish to initialize the static state
  // ahead of time.
  static void initialize();

private:
};

