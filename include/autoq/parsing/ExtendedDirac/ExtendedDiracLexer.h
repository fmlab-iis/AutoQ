
// Generated from src/ExtendedDirac/ExtendedDiracLexer.g4 by ANTLR 4.13.2

#pragma once


#include "antlr4-runtime.h"




class  ExtendedDiracLexer : public antlr4::Lexer {
public:
  enum {
    ADD = 1, BAR = 2, COMMA = 3, COLON = 4, DIV = 5, EQ = 6, LEFT_PARENTHESIS = 7, 
    LEFT_BRACE = 8, MUL = 9, NE = 10, NEWLINES = 11, OR = 12, POWER = 13, 
    PRIME = 14, PROD = 15, RIGHT_ANGLE_BRACKET = 16, RIGHT_PARENTHESIS = 17, 
    RIGHT_BRACE = 18, SEMICOLON = 19, SETMINUS = 20, STR = 21, SUB = 22, 
    SUM = 23, UNION = 24, WS = 25
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

  // Individual semantic predicate functions triggered by sempred() above.

};

