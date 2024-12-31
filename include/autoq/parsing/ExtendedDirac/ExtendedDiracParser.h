
// Generated from src/ExtendedDirac/ExtendedDiracParser.g4 by ANTLR 4.13.2

#pragma once


#include "antlr4-runtime.h"




class  ExtendedDiracParser : public antlr4::Parser {
public:
  enum {
    ADD = 1, BAR = 2, COMMA = 3, DIV = 4, DIGITS = 5, EI2PI = 6, EIPI = 7, 
    EQ = 8, INTERSECTION = 9, KET = 10, LEFT_BRACKET = 11, LEFT_CURLY_BRACKET = 12, 
    MUL = 13, NEWLINES = 14, POWER = 15, PROD = 16, RIGHT_BRACKET = 17, 
    RIGHT_CURLY_BRACKET = 18, SUB = 19, SETMINUS = 20, SQRT2 = 21, UNION = 22, 
    WHERE = 23, WS = 24, NAME = 25
  };

  enum {
    RuleExtendedDirac = 0, RuleMuloperators = 1, RuleMuloperator = 2, RuleAccepted = 3, 
    RuleSet = 4, RuleDiracs = 5, RuleDirac = 6, RuleCket = 7, RuleComplex = 8, 
    RuleAngle = 9, RuleIjklens = 10, RuleIjklen = 11
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
      std::set<std::string> predefinedVars;

      bool isNonZero(const std::string& text) {
          return std::stoi(text) != 0;
      }
      bool isASingleLetter(const std::string& text) {
          return text.length() == 1 && 'a' <= text.at(0) && text.at(0) <= 'z';
      }


  class ExtendedDiracContext;
  class MuloperatorsContext;
  class MuloperatorContext;
  class AcceptedContext;
  class SetContext;
  class DiracsContext;
  class DiracContext;
  class CketContext;
  class ComplexContext;
  class AngleContext;
  class IjklensContext;
  class IjklenContext; 

  class  ExtendedDiracContext : public antlr4::ParserRuleContext {
  public:
    ExtendedDiracContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    AcceptedContext *accepted();
    antlr4::tree::TerminalNode *WHERE();
    antlr4::tree::TerminalNode *NEWLINES();
    MuloperatorsContext *muloperators();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  ExtendedDiracContext* extendedDirac();

  class  MuloperatorsContext : public antlr4::ParserRuleContext {
  public:
    MuloperatorsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<MuloperatorContext *> muloperator();
    MuloperatorContext* muloperator(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  MuloperatorsContext* muloperators();

  class  MuloperatorContext : public antlr4::ParserRuleContext {
  public:
    MuloperatorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ComplexContext *> complex();
    ComplexContext* complex(size_t i);
    antlr4::tree::TerminalNode *PROD();
    antlr4::tree::TerminalNode *EQ();
    antlr4::tree::TerminalNode *NEWLINES();
    antlr4::tree::TerminalNode *EOF();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  MuloperatorContext* muloperator();

  class  AcceptedContext : public antlr4::ParserRuleContext {
  public:
    AcceptedContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<SetContext *> set();
    SetContext* set(size_t i);
    antlr4::tree::TerminalNode *SETMINUS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  AcceptedContext* accepted();

  class  SetContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *op = nullptr;
    antlr4::Token *n = nullptr;
    SetContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LEFT_BRACKET();
    std::vector<SetContext *> set();
    SetContext* set(size_t i);
    antlr4::tree::TerminalNode *RIGHT_BRACKET();
    antlr4::tree::TerminalNode *LEFT_CURLY_BRACKET();
    DiracsContext *diracs();
    antlr4::tree::TerminalNode *RIGHT_CURLY_BRACKET();
    DiracContext *dirac();
    antlr4::tree::TerminalNode *BAR();
    IjklensContext *ijklens();
    antlr4::tree::TerminalNode *PROD();
    antlr4::tree::TerminalNode *UNION();
    antlr4::tree::TerminalNode *INTERSECTION();
    antlr4::tree::TerminalNode *POWER();
    antlr4::tree::TerminalNode *DIGITS();

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
    antlr4::Token *op = nullptr;
    DiracContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    CketContext *cket();
    DiracContext *dirac();
    antlr4::tree::TerminalNode *ADD();
    antlr4::tree::TerminalNode *SUB();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  DiracContext* dirac();
  DiracContext* dirac(int precedence);
  class  CketContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *op = nullptr;
    antlr4::Token *ketToken = nullptr;
    CketContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *KET();
    ComplexContext *complex();
    antlr4::tree::TerminalNode *SUB();
    antlr4::tree::TerminalNode *MUL();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  CketContext* cket();

  class  ComplexContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *var = nullptr;
    antlr4::Token *op = nullptr;
    antlr4::Token *n = nullptr;
    ComplexContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LEFT_BRACKET();
    std::vector<ComplexContext *> complex();
    ComplexContext* complex(size_t i);
    antlr4::tree::TerminalNode *RIGHT_BRACKET();
    antlr4::tree::TerminalNode *SUB();
    antlr4::tree::TerminalNode *EI2PI();
    AngleContext *angle();
    antlr4::tree::TerminalNode *EIPI();
    antlr4::tree::TerminalNode *DIGITS();
    antlr4::tree::TerminalNode *SQRT2();
    antlr4::tree::TerminalNode *NAME();
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
  class  AngleContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *x = nullptr;
    antlr4::Token *y = nullptr;
    antlr4::Token *n = nullptr;
    AngleContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DIV();
    std::vector<antlr4::tree::TerminalNode *> DIGITS();
    antlr4::tree::TerminalNode* DIGITS(size_t i);
    antlr4::tree::TerminalNode *SUB();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  AngleContext* angle();

  class  IjklensContext : public antlr4::ParserRuleContext {
  public:
    IjklensContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IjklenContext *ijklen();
    IjklensContext *ijklens();
    antlr4::tree::TerminalNode *COMMA();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  IjklensContext* ijklens();
  IjklensContext* ijklens(int precedence);
  class  IjklenContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *var = nullptr;
    antlr4::Token *len = nullptr;
    IjklenContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> BAR();
    antlr4::tree::TerminalNode* BAR(size_t i);
    antlr4::tree::TerminalNode *EQ();
    antlr4::tree::TerminalNode *NAME();
    antlr4::tree::TerminalNode *DIGITS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  IjklenContext* ijklen();


  bool sempred(antlr4::RuleContext *_localctx, size_t ruleIndex, size_t predicateIndex) override;

  bool setSempred(SetContext *_localctx, size_t predicateIndex);
  bool diracsSempred(DiracsContext *_localctx, size_t predicateIndex);
  bool diracSempred(DiracContext *_localctx, size_t predicateIndex);
  bool complexSempred(ComplexContext *_localctx, size_t predicateIndex);
  bool angleSempred(AngleContext *_localctx, size_t predicateIndex);
  bool ijklensSempred(IjklensContext *_localctx, size_t predicateIndex);
  bool ijklenSempred(IjklenContext *_localctx, size_t predicateIndex);

  // By default the static state used to implement the parser is lazily initialized during the first
  // call to the constructor. You can call this function if you wish to initialize the static state
  // ahead of time.
  static void initialize();

private:
};

