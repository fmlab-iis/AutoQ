
// Generated from src/ExtendedDirac/ExtendedDiracLexer.g4 by ANTLR 4.13.2

#pragma once


#include "antlr4-runtime.h"




class  ExtendedDiracLexer : public antlr4::Lexer {
public:
  enum {
    ADD = 1, BAR = 2, COMMA = 3, DIV = 4, DIGITS = 5, EI2PI = 6, EIPI = 7, 
    EQ = 8, INTERSECTION = 9, KET = 10, LEFT_BRACKET = 11, LEFT_CURLY_BRACKET = 12, 
    MUL = 13, NEWLINES = 14, POWER = 15, PROD = 16, RIGHT_BRACKET = 17, 
    RIGHT_CURLY_BRACKET = 18, SUB = 19, SETMINUS = 20, SQRT2 = 21, UNION = 22, 
    WHERE = 23, WS = 24, NAME = 25
  };

  explicit ExtendedDiracLexer(antlr4::CharStream *input);

  ~ExtendedDiracLexer() override;


      bool skipNewline = true;


  std::string getGrammarFileName() const override;

  const std::vector<std::string>& getRuleNames() const override;

  const std::vector<std::string>& getChannelNames() const override;

  const std::vector<std::string>& getModeNames() const override;

  const antlr4::dfa::Vocabulary& getVocabulary() const override;

  antlr4::atn::SerializedATNView getSerializedATN() const override;

  const antlr4::atn::ATN& getATN() const override;

  void action(antlr4::RuleContext *context, size_t ruleIndex, size_t actionIndex) override;

  // By default the static state used to implement the lexer is lazily initialized during the first
  // call to the constructor. You can call this function if you wish to initialize the static state
  // ahead of time.
  static void initialize();

private:

  // Individual action functions triggered by action() above.
  void NEWLINESAction(antlr4::RuleContext *context, size_t actionIndex);
  void WHEREAction(antlr4::RuleContext *context, size_t actionIndex);

  // Individual semantic predicate functions triggered by sempred() above.

};

