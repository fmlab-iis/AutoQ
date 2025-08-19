
// Generated from src/ExtendedDirac/ExtendedDiracLexer.g4 by ANTLR 4.13.2


#include "ExtendedDiracLexer.h"


using namespace antlr4;



using namespace antlr4;

namespace {

struct ExtendedDiracLexerStaticData final {
  ExtendedDiracLexerStaticData(std::vector<std::string> ruleNames,
                          std::vector<std::string> channelNames,
                          std::vector<std::string> modeNames,
                          std::vector<std::string> literalNames,
                          std::vector<std::string> symbolicNames)
      : ruleNames(std::move(ruleNames)), channelNames(std::move(channelNames)),
        modeNames(std::move(modeNames)), literalNames(std::move(literalNames)),
        symbolicNames(std::move(symbolicNames)),
        vocabulary(this->literalNames, this->symbolicNames) {}

  ExtendedDiracLexerStaticData(const ExtendedDiracLexerStaticData&) = delete;
  ExtendedDiracLexerStaticData(ExtendedDiracLexerStaticData&&) = delete;
  ExtendedDiracLexerStaticData& operator=(const ExtendedDiracLexerStaticData&) = delete;
  ExtendedDiracLexerStaticData& operator=(ExtendedDiracLexerStaticData&&) = delete;

  std::vector<antlr4::dfa::DFA> decisionToDFA;
  antlr4::atn::PredictionContextCache sharedContextCache;
  const std::vector<std::string> ruleNames;
  const std::vector<std::string> channelNames;
  const std::vector<std::string> modeNames;
  const std::vector<std::string> literalNames;
  const std::vector<std::string> symbolicNames;
  const antlr4::dfa::Vocabulary vocabulary;
  antlr4::atn::SerializedATNView serializedATN;
  std::unique_ptr<antlr4::atn::ATN> atn;
};

::antlr4::internal::OnceFlag extendeddiraclexerLexerOnceFlag;
#if ANTLR4_USE_THREAD_LOCAL_CACHE
static thread_local
#endif
std::unique_ptr<ExtendedDiracLexerStaticData> extendeddiraclexerLexerStaticData = nullptr;

void extendeddiraclexerLexerInitialize() {
#if ANTLR4_USE_THREAD_LOCAL_CACHE
  if (extendeddiraclexerLexerStaticData != nullptr) {
    return;
  }
#else
  assert(extendeddiraclexerLexerStaticData == nullptr);
#endif
  auto staticData = std::make_unique<ExtendedDiracLexerStaticData>(
    std::vector<std::string>{
      "ADD", "BAR", "COMMA", "COLON", "DIV", "EQ", "LEFT_PARENTHESIS", "LEFT_BRACE", 
      "MUL", "NE", "NEWLINES", "OR", "POWER", "PRIME", "PROD", "RIGHT_ANGLE_BRACKET", 
      "RIGHT_PARENTHESIS", "RIGHT_BRACE", "SEMICOLON", "SETMINUS", "STR", 
      "SUB", "SUM", "UNION", "WS"
    },
    std::vector<std::string>{
      "DEFAULT_TOKEN_CHANNEL", "HIDDEN"
    },
    std::vector<std::string>{
      "DEFAULT_MODE"
    },
    std::vector<std::string>{
      "", "'+'", "'|'", "','", "':'", "'/'", "'='", "'('", "'{'", "'*'", 
      "'\\u2260'", "", "'\\u2228'", "'^'", "'''", "'\\u2297'", "", "')'", 
      "'}'", "';'", "'\\'", "", "'-'", "", "'\\u222A'"
    },
    std::vector<std::string>{
      "", "ADD", "BAR", "COMMA", "COLON", "DIV", "EQ", "LEFT_PARENTHESIS", 
      "LEFT_BRACE", "MUL", "NE", "NEWLINES", "OR", "POWER", "PRIME", "PROD", 
      "RIGHT_ANGLE_BRACKET", "RIGHT_PARENTHESIS", "RIGHT_BRACE", "SEMICOLON", 
      "SETMINUS", "STR", "SUB", "SUM", "UNION", "WS"
    }
  );
  static const int32_t serializedATNSegment[] = {
  	4,0,25,116,6,-1,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,
  	6,2,7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,2,11,7,11,2,12,7,12,2,13,7,13,2,14,
  	7,14,2,15,7,15,2,16,7,16,2,17,7,17,2,18,7,18,2,19,7,19,2,20,7,20,2,21,
  	7,21,2,22,7,22,2,23,7,23,2,24,7,24,1,0,1,0,1,1,1,1,1,2,1,2,1,3,1,3,1,
  	4,1,4,1,5,1,5,1,6,1,6,1,7,1,7,1,8,1,8,1,9,1,9,1,10,4,10,73,8,10,11,10,
  	12,10,74,1,10,1,10,1,11,1,11,1,12,1,12,1,13,1,13,1,14,1,14,1,15,1,15,
  	1,16,1,16,1,17,1,17,1,18,1,18,1,19,1,19,1,20,1,20,1,20,4,20,100,8,20,
  	11,20,12,20,101,1,21,1,21,1,22,1,22,1,23,1,23,1,24,4,24,111,8,24,11,24,
  	12,24,112,1,24,1,24,0,0,25,1,1,3,2,5,3,7,4,9,5,11,6,13,7,15,8,17,9,19,
  	10,21,11,23,12,25,13,27,14,29,15,31,16,33,17,35,18,37,19,39,20,41,21,
  	43,22,45,23,47,24,49,25,1,0,6,2,0,10,10,13,13,2,0,62,62,10217,10217,3,
  	0,48,57,65,90,97,122,1,0,97,122,2,0,931,931,8721,8721,2,0,9,9,32,32,119,
  	0,1,1,0,0,0,0,3,1,0,0,0,0,5,1,0,0,0,0,7,1,0,0,0,0,9,1,0,0,0,0,11,1,0,
  	0,0,0,13,1,0,0,0,0,15,1,0,0,0,0,17,1,0,0,0,0,19,1,0,0,0,0,21,1,0,0,0,
  	0,23,1,0,0,0,0,25,1,0,0,0,0,27,1,0,0,0,0,29,1,0,0,0,0,31,1,0,0,0,0,33,
  	1,0,0,0,0,35,1,0,0,0,0,37,1,0,0,0,0,39,1,0,0,0,0,41,1,0,0,0,0,43,1,0,
  	0,0,0,45,1,0,0,0,0,47,1,0,0,0,0,49,1,0,0,0,1,51,1,0,0,0,3,53,1,0,0,0,
  	5,55,1,0,0,0,7,57,1,0,0,0,9,59,1,0,0,0,11,61,1,0,0,0,13,63,1,0,0,0,15,
  	65,1,0,0,0,17,67,1,0,0,0,19,69,1,0,0,0,21,72,1,0,0,0,23,78,1,0,0,0,25,
  	80,1,0,0,0,27,82,1,0,0,0,29,84,1,0,0,0,31,86,1,0,0,0,33,88,1,0,0,0,35,
  	90,1,0,0,0,37,92,1,0,0,0,39,94,1,0,0,0,41,99,1,0,0,0,43,103,1,0,0,0,45,
  	105,1,0,0,0,47,107,1,0,0,0,49,110,1,0,0,0,51,52,5,43,0,0,52,2,1,0,0,0,
  	53,54,5,124,0,0,54,4,1,0,0,0,55,56,5,44,0,0,56,6,1,0,0,0,57,58,5,58,0,
  	0,58,8,1,0,0,0,59,60,5,47,0,0,60,10,1,0,0,0,61,62,5,61,0,0,62,12,1,0,
  	0,0,63,64,5,40,0,0,64,14,1,0,0,0,65,66,5,123,0,0,66,16,1,0,0,0,67,68,
  	5,42,0,0,68,18,1,0,0,0,69,70,5,8800,0,0,70,20,1,0,0,0,71,73,7,0,0,0,72,
  	71,1,0,0,0,73,74,1,0,0,0,74,72,1,0,0,0,74,75,1,0,0,0,75,76,1,0,0,0,76,
  	77,6,10,0,0,77,22,1,0,0,0,78,79,5,8744,0,0,79,24,1,0,0,0,80,81,5,94,0,
  	0,81,26,1,0,0,0,82,83,5,39,0,0,83,28,1,0,0,0,84,85,5,8855,0,0,85,30,1,
  	0,0,0,86,87,7,1,0,0,87,32,1,0,0,0,88,89,5,41,0,0,89,34,1,0,0,0,90,91,
  	5,125,0,0,91,36,1,0,0,0,92,93,5,59,0,0,93,38,1,0,0,0,94,95,5,92,0,0,95,
  	40,1,0,0,0,96,100,7,2,0,0,97,98,7,3,0,0,98,100,3,27,13,0,99,96,1,0,0,
  	0,99,97,1,0,0,0,100,101,1,0,0,0,101,99,1,0,0,0,101,102,1,0,0,0,102,42,
  	1,0,0,0,103,104,5,45,0,0,104,44,1,0,0,0,105,106,7,4,0,0,106,46,1,0,0,
  	0,107,108,5,8746,0,0,108,48,1,0,0,0,109,111,7,5,0,0,110,109,1,0,0,0,111,
  	112,1,0,0,0,112,110,1,0,0,0,112,113,1,0,0,0,113,114,1,0,0,0,114,115,6,
  	24,1,0,115,50,1,0,0,0,5,0,74,99,101,112,2,1,10,0,6,0,0
  };
  staticData->serializedATN = antlr4::atn::SerializedATNView(serializedATNSegment, sizeof(serializedATNSegment) / sizeof(serializedATNSegment[0]));

  antlr4::atn::ATNDeserializer deserializer;
  staticData->atn = deserializer.deserialize(staticData->serializedATN);

  const size_t count = staticData->atn->getNumberOfDecisions();
  staticData->decisionToDFA.reserve(count);
  for (size_t i = 0; i < count; i++) { 
    staticData->decisionToDFA.emplace_back(staticData->atn->getDecisionState(i), i);
  }
  extendeddiraclexerLexerStaticData = std::move(staticData);
}

}

ExtendedDiracLexer::ExtendedDiracLexer(CharStream *input) : Lexer(input) {
  ExtendedDiracLexer::initialize();
  _interpreter = new atn::LexerATNSimulator(this, *extendeddiraclexerLexerStaticData->atn, extendeddiraclexerLexerStaticData->decisionToDFA, extendeddiraclexerLexerStaticData->sharedContextCache);
}

ExtendedDiracLexer::~ExtendedDiracLexer() {
  delete _interpreter;
}

std::string ExtendedDiracLexer::getGrammarFileName() const {
  return "ExtendedDiracLexer.g4";
}

const std::vector<std::string>& ExtendedDiracLexer::getRuleNames() const {
  return extendeddiraclexerLexerStaticData->ruleNames;
}

const std::vector<std::string>& ExtendedDiracLexer::getChannelNames() const {
  return extendeddiraclexerLexerStaticData->channelNames;
}

const std::vector<std::string>& ExtendedDiracLexer::getModeNames() const {
  return extendeddiraclexerLexerStaticData->modeNames;
}

const dfa::Vocabulary& ExtendedDiracLexer::getVocabulary() const {
  return extendeddiraclexerLexerStaticData->vocabulary;
}

antlr4::atn::SerializedATNView ExtendedDiracLexer::getSerializedATN() const {
  return extendeddiraclexerLexerStaticData->serializedATN;
}

const atn::ATN& ExtendedDiracLexer::getATN() const {
  return *extendeddiraclexerLexerStaticData->atn;
}


void ExtendedDiracLexer::action(RuleContext *context, size_t ruleIndex, size_t actionIndex) {
  switch (ruleIndex) {
    case 10: NEWLINESAction(antlrcpp::downCast<antlr4::RuleContext *>(context), actionIndex); break;

  default:
    break;
  }
}

void ExtendedDiracLexer::NEWLINESAction(antlr4::RuleContext *context, size_t actionIndex) {
  switch (actionIndex) {
    case 0:  if (skipNewline) skip();  break;

  default:
    break;
  }
}



void ExtendedDiracLexer::initialize() {
#if ANTLR4_USE_THREAD_LOCAL_CACHE
  extendeddiraclexerLexerInitialize();
#else
  ::antlr4::internal::call_once(extendeddiraclexerLexerOnceFlag, extendeddiraclexerLexerInitialize);
#endif
}
