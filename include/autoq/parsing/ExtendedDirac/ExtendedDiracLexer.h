
// Generated from src/ExtendedDirac/ExtendedDiracLexer.g4 by ANTLR 4.13.2

#pragma once


#include "antlr4-runtime.h"




class  ExtendedDiracLexer : public antlr4::Lexer {
public:
  enum {
    ADD = 1, BAR = 2, COMMA = 3, COLON = 4, EQ = 5, LEFT_BRACE = 6, NE = 7, 
    NEWLINES = 8, OR = 9, POWER = 10, PRIME = 11, PROD = 12, RIGHT_ANGLE_BRACKET = 13, 
    RIGHT_BRACE = 14, SEMICOLON = 15, STR = 16, SUM = 17, UNION = 18, WS = 19
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

