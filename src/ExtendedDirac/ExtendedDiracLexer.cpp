
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
      "ADD", "BAR", "COMMA", "COLON", "EQ", "LEFT_BRACE", "NE", "NEWLINES", 
      "OR", "POWER", "PRIME", "PROD", "RIGHT_ANGLE_BRACKET", "RIGHT_BRACE", 
      "SEMICOLON", "STR", "SUM", "UNION", "WS"
    },
    std::vector<std::string>{
      "DEFAULT_TOKEN_CHANNEL", "HIDDEN"
    },
    std::vector<std::string>{
      "DEFAULT_MODE"
    },
    std::vector<std::string>{
      "", "'+'", "'|'", "','", "':'", "'='", "'{'", "'\\u2260'", "", "'\\u2228'", 
      "'^'", "'''", "'\\u2297'", "", "'}'", "';'", "", "", "'\\u222A'"
    },
    std::vector<std::string>{
      "", "ADD", "BAR", "COMMA", "COLON", "EQ", "LEFT_BRACE", "NE", "NEWLINES", 
      "OR", "POWER", "PRIME", "PROD", "RIGHT_ANGLE_BRACKET", "RIGHT_BRACE", 
      "SEMICOLON", "STR", "SUM", "UNION", "WS"
    }
  );
  static const int32_t serializedATNSegment[] = {
  	4,0,19,92,6,-1,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,
  	6,2,7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,2,11,7,11,2,12,7,12,2,13,7,13,2,14,
  	7,14,2,15,7,15,2,16,7,16,2,17,7,17,2,18,7,18,1,0,1,0,1,1,1,1,1,2,1,2,
  	1,3,1,3,1,4,1,4,1,5,1,5,1,6,1,6,1,7,4,7,55,8,7,11,7,12,7,56,1,7,1,7,1,
  	8,1,8,1,9,1,9,1,10,1,10,1,11,1,11,1,12,1,12,1,13,1,13,1,14,1,14,1,15,
  	1,15,1,15,4,15,78,8,15,11,15,12,15,79,1,16,1,16,1,17,1,17,1,18,4,18,87,
  	8,18,11,18,12,18,88,1,18,1,18,0,0,19,1,1,3,2,5,3,7,4,9,5,11,6,13,7,15,
  	8,17,9,19,10,21,11,23,12,25,13,27,14,29,15,31,16,33,17,35,18,37,19,1,
  	0,6,2,0,10,10,13,13,2,0,62,62,10217,10217,3,0,48,57,65,90,97,122,1,0,
  	97,122,2,0,931,931,8721,8721,2,0,9,9,32,32,95,0,1,1,0,0,0,0,3,1,0,0,0,
  	0,5,1,0,0,0,0,7,1,0,0,0,0,9,1,0,0,0,0,11,1,0,0,0,0,13,1,0,0,0,0,15,1,
  	0,0,0,0,17,1,0,0,0,0,19,1,0,0,0,0,21,1,0,0,0,0,23,1,0,0,0,0,25,1,0,0,
  	0,0,27,1,0,0,0,0,29,1,0,0,0,0,31,1,0,0,0,0,33,1,0,0,0,0,35,1,0,0,0,0,
  	37,1,0,0,0,1,39,1,0,0,0,3,41,1,0,0,0,5,43,1,0,0,0,7,45,1,0,0,0,9,47,1,
  	0,0,0,11,49,1,0,0,0,13,51,1,0,0,0,15,54,1,0,0,0,17,60,1,0,0,0,19,62,1,
  	0,0,0,21,64,1,0,0,0,23,66,1,0,0,0,25,68,1,0,0,0,27,70,1,0,0,0,29,72,1,
  	0,0,0,31,77,1,0,0,0,33,81,1,0,0,0,35,83,1,0,0,0,37,86,1,0,0,0,39,40,5,
  	43,0,0,40,2,1,0,0,0,41,42,5,124,0,0,42,4,1,0,0,0,43,44,5,44,0,0,44,6,
  	1,0,0,0,45,46,5,58,0,0,46,8,1,0,0,0,47,48,5,61,0,0,48,10,1,0,0,0,49,50,
  	5,123,0,0,50,12,1,0,0,0,51,52,5,8800,0,0,52,14,1,0,0,0,53,55,7,0,0,0,
  	54,53,1,0,0,0,55,56,1,0,0,0,56,54,1,0,0,0,56,57,1,0,0,0,57,58,1,0,0,0,
  	58,59,6,7,0,0,59,16,1,0,0,0,60,61,5,8744,0,0,61,18,1,0,0,0,62,63,5,94,
  	0,0,63,20,1,0,0,0,64,65,5,39,0,0,65,22,1,0,0,0,66,67,5,8855,0,0,67,24,
  	1,0,0,0,68,69,7,1,0,0,69,26,1,0,0,0,70,71,5,125,0,0,71,28,1,0,0,0,72,
  	73,5,59,0,0,73,30,1,0,0,0,74,78,7,2,0,0,75,76,7,3,0,0,76,78,3,21,10,0,
  	77,74,1,0,0,0,77,75,1,0,0,0,78,79,1,0,0,0,79,77,1,0,0,0,79,80,1,0,0,0,
  	80,32,1,0,0,0,81,82,7,4,0,0,82,34,1,0,0,0,83,84,5,8746,0,0,84,36,1,0,
  	0,0,85,87,7,5,0,0,86,85,1,0,0,0,87,88,1,0,0,0,88,86,1,0,0,0,88,89,1,0,
  	0,0,89,90,1,0,0,0,90,91,6,18,1,0,91,38,1,0,0,0,5,0,56,77,79,88,2,1,7,
  	0,6,0,0
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
    case 7: NEWLINESAction(antlrcpp::downCast<antlr4::RuleContext *>(context), actionIndex); break;

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
