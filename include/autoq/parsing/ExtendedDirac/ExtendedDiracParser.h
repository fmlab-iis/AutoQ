
// Generated from src/ExtendedDirac/ExtendedDiracParser.g4 by ANTLR 4.13.2

#pragma once


#include "antlr4-runtime.h"




class  ExtendedDiracParser : public antlr4::Parser {
public:
  enum {
    ADD = 1, BAR = 2, COMMA = 3, COLON = 4, EQ = 5, LEFT_BRACE = 6, NE = 7, 
    NEWLINES = 8, OR = 9, POWER = 10, PRIME = 11, PROD = 12, RIGHT_ANGLE_BRACKET = 13, 
    RIGHT_BRACE = 14, SEMICOLON = 15, SETMINUS = 16, STR = 17, SUM = 18, 
    UNION = 19, WS = 20
  };

  enum {
    RuleExpr = 0, RuleTset = 1, RuleSet = 2, RuleDiracs = 3, RuleDirac = 4, 
    RuleTerm = 5, RuleVarcons = 6, RuleVarcon = 7, RuleIneq = 8
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
      bool isALowercaseLetter(const std::string& text) {
          return text.length() == 1 && 'a' <= text.at(0) && text.at(0) <= 'z';
      }
      bool isAConstantBinaryString(const std::string& text) {
          return std::all_of(text.begin(), text.end(), [](char c) { return c == '0' || c == '1'; });
      }


  class ExprContext;
  class TsetContext;
  class SetContext;
  class DiracsContext;
  class DiracContext;
  class TermContext;
  class VarconsContext;
  class VarconContext;
  class IneqContext; 

  class  ExprContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *op = nullptr;
    ExprContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<TsetContext *> tset();
    TsetContext* tset(size_t i);
    antlr4::tree::TerminalNode *SETMINUS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  ExprContext* expr();

  class  TsetContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *op = nullptr;
    antlr4::Token *N = nullptr;
    TsetContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<SetContext *> set();
    SetContext* set(size_t i);
    antlr4::tree::TerminalNode *POWER();
    antlr4::tree::TerminalNode *STR();
    std::vector<antlr4::tree::TerminalNode *> SEMICOLON();
    antlr4::tree::TerminalNode* SEMICOLON(size_t i);
    std::vector<TsetContext *> tset();
    TsetContext* tset(size_t i);
    antlr4::tree::TerminalNode *PROD();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  TsetContext* tset();
  TsetContext* tset(int precedence);
  class  SetContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *op = nullptr;
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
    antlr4::Token *op = nullptr;
    DiracContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    TermContext *term();
    DiracContext *dirac();
    antlr4::tree::TerminalNode *ADD();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  DiracContext* dirac();
  DiracContext* dirac(int precedence);
  class  TermContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *C = nullptr;
    antlr4::Token *VStr = nullptr;
    TermContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *BAR();
    antlr4::tree::TerminalNode *RIGHT_ANGLE_BRACKET();
    std::vector<antlr4::tree::TerminalNode *> STR();
    antlr4::tree::TerminalNode* STR(size_t i);
    antlr4::tree::TerminalNode *SUM();
    VarconsContext *varcons();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  TermContext* term();

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
    antlr4::Token *CStr = nullptr;
    VarconContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> BAR();
    antlr4::tree::TerminalNode* BAR(size_t i);
    antlr4::tree::TerminalNode *EQ();
    std::vector<antlr4::tree::TerminalNode *> STR();
    antlr4::tree::TerminalNode* STR(size_t i);
    IneqContext *ineq();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  VarconContext* varcon();

  class  IneqContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *L = nullptr;
    antlr4::Token *R = nullptr;
    IneqContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *NE();
    std::vector<antlr4::tree::TerminalNode *> STR();
    antlr4::tree::TerminalNode* STR(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;

    virtual std::any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  IneqContext* ineq();


  bool sempred(antlr4::RuleContext *_localctx, size_t ruleIndex, size_t predicateIndex) override;

  bool tsetSempred(TsetContext *_localctx, size_t predicateIndex);
  bool setSempred(SetContext *_localctx, size_t predicateIndex);
  bool diracsSempred(DiracsContext *_localctx, size_t predicateIndex);
  bool diracSempred(DiracContext *_localctx, size_t predicateIndex);
  bool varconsSempred(VarconsContext *_localctx, size_t predicateIndex);
  bool varconSempred(VarconContext *_localctx, size_t predicateIndex);
  bool ineqSempred(IneqContext *_localctx, size_t predicateIndex);

  // By default the static state used to implement the parser is lazily initialized during the first
  // call to the constructor. You can call this function if you wish to initialize the static state
  // ahead of time.
  static void initialize();

private:
};

