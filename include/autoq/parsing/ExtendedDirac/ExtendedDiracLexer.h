
// Generated from src/ExtendedDirac/ExtendedDiracLexer.g4 by ANTLR 4.13.2

#pragma once


#include "antlr4-runtime.h"




class  ExtendedDiracLexer : public antlr4::Lexer {
public:
  enum {
    ADD = 1, BAR = 2, COMMA = 3, DIV = 4, DIGITS = 5, EI2PI = 6, EIPI = 7, 
    EQ = 8, INTERSECTION = 9, KET = 10, LEFT_BRACKET = 11, LEFT_CURLY_BRACKET = 12, 
    MUL = 13, POWER = 14, PROD = 15, RIGHT_BRACKET = 16, RIGHT_CURLY_BRACKET = 17, 
    SUB = 18, SETMINUS = 19, SQRT2 = 20, UNION = 21, WS = 22, NAME = 23
  };

  explicit ExtendedDiracLexer(antlr4::CharStream *input);

  ~ExtendedDiracLexer() override;


  std::string getGrammarFileName() const override;

  const std::vector<std::string>& getRuleNames() const override;

  const std::vector<std::string>& getChannelNames() const override;

  const std::vector<std::string>& getModeNames() const override;

  const antlr4::dfa::Vocabulary& getVocabulary() const override;

  antlr4::atn::SerializedATNView getSerializedATN() const override;

  const antlr4::atn::ATN& getATN() const override;

  // By default the static state used to implement the lexer is lazily initialized during the first
  // call to the constructor. You can call this function if you wish to initialize the static state
  // ahead of time.
  static void initialize();

private:

  // Individual action functions triggered by action() above.

  // Individual semantic predicate functions triggered by sempred() above.

};

