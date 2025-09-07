
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
      "MUL", "NE", "NEWLINES", "POWER", "PRIME", "PROD", "RIGHT_ANGLE_BRACKET", 
      "RIGHT_PARENTHESIS", "RIGHT_BRACE", "SEMICOLON", "SETMINUS", "STR", 
      "SUB", "SUM", "UNION", "WS", "LOGICAL_AND", "LOGICAL_OR", "LOGICAL_NOT", 
      "LESS_THAN", "LESS_EQUAL", "GREATER_EQUAL"
    },
    std::vector<std::string>{
      "DEFAULT_TOKEN_CHANNEL", "HIDDEN"
    },
    std::vector<std::string>{
      "DEFAULT_MODE"
    },
    std::vector<std::string>{
      "", "'+'", "'|'", "','", "':'", "'/'", "'='", "'('", "'{'", "'*'", 
      "", "", "'^'", "'''", "'\\u2297'", "", "')'", "'}'", "';'", "'\\'", 
      "", "'-'", "", "'\\u222A'", "", "", "", "", "'<'"
    },
    std::vector<std::string>{
      "", "ADD", "BAR", "COMMA", "COLON", "DIV", "EQ", "LEFT_PARENTHESIS", 
      "LEFT_BRACE", "MUL", "NE", "NEWLINES", "POWER", "PRIME", "PROD", "RIGHT_ANGLE_BRACKET", 
      "RIGHT_PARENTHESIS", "RIGHT_BRACE", "SEMICOLON", "SETMINUS", "STR", 
      "SUB", "SUM", "UNION", "WS", "LOGICAL_AND", "LOGICAL_OR", "LOGICAL_NOT", 
      "LESS_THAN", "LESS_EQUAL", "GREATER_EQUAL"
    }
  );
  static const int32_t serializedATNSegment[] = {
  	4,0,30,151,6,-1,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,
  	6,2,7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,2,11,7,11,2,12,7,12,2,13,7,13,2,14,
  	7,14,2,15,7,15,2,16,7,16,2,17,7,17,2,18,7,18,2,19,7,19,2,20,7,20,2,21,
  	7,21,2,22,7,22,2,23,7,23,2,24,7,24,2,25,7,25,2,26,7,26,2,27,7,27,2,28,
  	7,28,2,29,7,29,1,0,1,0,1,1,1,1,1,2,1,2,1,3,1,3,1,4,1,4,1,5,1,5,1,6,1,
  	6,1,7,1,7,1,8,1,8,1,9,1,9,1,9,3,9,83,8,9,1,10,4,10,86,8,10,11,10,12,10,
  	87,1,10,1,10,1,11,1,11,1,12,1,12,1,13,1,13,1,14,1,14,1,15,1,15,1,16,1,
  	16,1,17,1,17,1,18,1,18,1,19,1,19,1,19,4,19,111,8,19,11,19,12,19,112,1,
  	20,1,20,1,21,1,21,1,22,1,22,1,23,4,23,122,8,23,11,23,12,23,123,1,23,1,
  	23,1,24,1,24,1,24,3,24,131,8,24,1,25,1,25,1,25,3,25,136,8,25,1,26,1,26,
  	1,27,1,27,1,28,1,28,1,28,3,28,145,8,28,1,29,1,29,1,29,3,29,150,8,29,0,
  	0,30,1,1,3,2,5,3,7,4,9,5,11,6,13,7,15,8,17,9,19,10,21,11,23,12,25,13,
  	27,14,29,15,31,16,33,17,35,18,37,19,39,20,41,21,43,22,45,23,47,24,49,
  	25,51,26,53,27,55,28,57,29,59,30,1,0,9,2,0,10,10,13,13,2,0,62,62,10217,
  	10217,3,0,48,57,65,90,97,122,1,0,97,122,2,0,931,931,8721,8721,2,0,9,9,
  	32,32,2,0,33,33,172,172,2,0,8804,8804,8806,8806,2,0,8805,8805,8807,8807,
  	159,0,1,1,0,0,0,0,3,1,0,0,0,0,5,1,0,0,0,0,7,1,0,0,0,0,9,1,0,0,0,0,11,
  	1,0,0,0,0,13,1,0,0,0,0,15,1,0,0,0,0,17,1,0,0,0,0,19,1,0,0,0,0,21,1,0,
  	0,0,0,23,1,0,0,0,0,25,1,0,0,0,0,27,1,0,0,0,0,29,1,0,0,0,0,31,1,0,0,0,
  	0,33,1,0,0,0,0,35,1,0,0,0,0,37,1,0,0,0,0,39,1,0,0,0,0,41,1,0,0,0,0,43,
  	1,0,0,0,0,45,1,0,0,0,0,47,1,0,0,0,0,49,1,0,0,0,0,51,1,0,0,0,0,53,1,0,
  	0,0,0,55,1,0,0,0,0,57,1,0,0,0,0,59,1,0,0,0,1,61,1,0,0,0,3,63,1,0,0,0,
  	5,65,1,0,0,0,7,67,1,0,0,0,9,69,1,0,0,0,11,71,1,0,0,0,13,73,1,0,0,0,15,
  	75,1,0,0,0,17,77,1,0,0,0,19,82,1,0,0,0,21,85,1,0,0,0,23,91,1,0,0,0,25,
  	93,1,0,0,0,27,95,1,0,0,0,29,97,1,0,0,0,31,99,1,0,0,0,33,101,1,0,0,0,35,
  	103,1,0,0,0,37,105,1,0,0,0,39,110,1,0,0,0,41,114,1,0,0,0,43,116,1,0,0,
  	0,45,118,1,0,0,0,47,121,1,0,0,0,49,130,1,0,0,0,51,135,1,0,0,0,53,137,
  	1,0,0,0,55,139,1,0,0,0,57,144,1,0,0,0,59,149,1,0,0,0,61,62,5,43,0,0,62,
  	2,1,0,0,0,63,64,5,124,0,0,64,4,1,0,0,0,65,66,5,44,0,0,66,6,1,0,0,0,67,
  	68,5,58,0,0,68,8,1,0,0,0,69,70,5,47,0,0,70,10,1,0,0,0,71,72,5,61,0,0,
  	72,12,1,0,0,0,73,74,5,40,0,0,74,14,1,0,0,0,75,76,5,123,0,0,76,16,1,0,
  	0,0,77,78,5,42,0,0,78,18,1,0,0,0,79,83,5,8800,0,0,80,81,5,33,0,0,81,83,
  	5,61,0,0,82,79,1,0,0,0,82,80,1,0,0,0,83,20,1,0,0,0,84,86,7,0,0,0,85,84,
  	1,0,0,0,86,87,1,0,0,0,87,85,1,0,0,0,87,88,1,0,0,0,88,89,1,0,0,0,89,90,
  	6,10,0,0,90,22,1,0,0,0,91,92,5,94,0,0,92,24,1,0,0,0,93,94,5,39,0,0,94,
  	26,1,0,0,0,95,96,5,8855,0,0,96,28,1,0,0,0,97,98,7,1,0,0,98,30,1,0,0,0,
  	99,100,5,41,0,0,100,32,1,0,0,0,101,102,5,125,0,0,102,34,1,0,0,0,103,104,
  	5,59,0,0,104,36,1,0,0,0,105,106,5,92,0,0,106,38,1,0,0,0,107,111,7,2,0,
  	0,108,109,7,3,0,0,109,111,3,25,12,0,110,107,1,0,0,0,110,108,1,0,0,0,111,
  	112,1,0,0,0,112,110,1,0,0,0,112,113,1,0,0,0,113,40,1,0,0,0,114,115,5,
  	45,0,0,115,42,1,0,0,0,116,117,7,4,0,0,117,44,1,0,0,0,118,119,5,8746,0,
  	0,119,46,1,0,0,0,120,122,7,5,0,0,121,120,1,0,0,0,122,123,1,0,0,0,123,
  	121,1,0,0,0,123,124,1,0,0,0,124,125,1,0,0,0,125,126,6,23,1,0,126,48,1,
  	0,0,0,127,128,5,38,0,0,128,131,5,38,0,0,129,131,5,8743,0,0,130,127,1,
  	0,0,0,130,129,1,0,0,0,131,50,1,0,0,0,132,133,5,124,0,0,133,136,5,124,
  	0,0,134,136,5,8744,0,0,135,132,1,0,0,0,135,134,1,0,0,0,136,52,1,0,0,0,
  	137,138,7,6,0,0,138,54,1,0,0,0,139,140,5,60,0,0,140,56,1,0,0,0,141,142,
  	5,60,0,0,142,145,5,61,0,0,143,145,7,7,0,0,144,141,1,0,0,0,144,143,1,0,
  	0,0,145,58,1,0,0,0,146,147,5,62,0,0,147,150,5,61,0,0,148,150,7,8,0,0,
  	149,146,1,0,0,0,149,148,1,0,0,0,150,60,1,0,0,0,10,0,82,87,110,112,123,
  	130,135,144,149,2,1,10,0,6,0,0
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
