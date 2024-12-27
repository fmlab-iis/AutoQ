
// Generated from src/ExtendedDirac/ExtendedDirac.g4 by ANTLR 4.13.2

#pragma once


#include "antlr4-runtime.h"




class  ExtendedDiracParser : public antlr4::Parser {
public:
  enum {
    T__0 = 1, T__1 = 2, T__2 = 3, T__3 = 4, T__4 = 5, T__5 = 6, T__6 = 7, 
    T__7 = 8, T__8 = 9, T__9 = 10, T__10 = 11, T__11 = 12, ADD = 13, DIV = 14, 
    DIGITS = 15, INTERSECTION = 16, KET = 17, MUL = 18, NAME = 19, PROD = 20, 
    SUB = 21, UNION = 22, WS = 23
  };

  enum {
    RuleExtendedDirac = 0, RuleSet = 1, RuleDiracs = 2, RuleDirac = 3, RuleCket = 4, 
    RuleComplex = 5, RuleAngle = 6, RuleIjklens = 7, RuleIjklen = 8
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
    std::vector<SetContext *> set();
    SetContext* set(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  ExtendedDiracContext* extendedDirac();

  class  SetContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *op = nullptr;
    antlr4::Token *n = nullptr;
    SetContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<SetContext *> set();
    SetContext* set(size_t i);
    DiracsContext *diracs();
    DiracContext *dirac();
    IjklensContext *ijklens();
    antlr4::tree::TerminalNode *PROD();
    antlr4::tree::TerminalNode *UNION();
    antlr4::tree::TerminalNode *INTERSECTION();
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
    std::vector<ComplexContext *> complex();
    ComplexContext* complex(size_t i);
    antlr4::tree::TerminalNode *SUB();
    AngleContext *angle();
    antlr4::tree::TerminalNode *DIGITS();
    antlr4::tree::TerminalNode *NAME();
    antlr4::tree::TerminalNode *MUL();
    antlr4::tree::TerminalNode *DIV();
    antlr4::tree::TerminalNode *ADD();

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

