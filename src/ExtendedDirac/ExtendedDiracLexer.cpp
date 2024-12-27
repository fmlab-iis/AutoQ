
// Generated from src/ExtendedDirac/ExtendedDirac.g4 by ANTLR 4.13.2


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
      "T__0", "T__1", "T__2", "T__3", "T__4", "T__5", "T__6", "T__7", "T__8", 
      "T__9", "T__10", "T__11", "ADD", "DIV", "DIGITS", "INTERSECTION", 
      "KET", "MUL", "NAME", "PROD", "SUB", "UNION", "WS"
    },
    std::vector<std::string>{
      "DEFAULT_TOKEN_CHANNEL", "HIDDEN"
    },
    std::vector<std::string>{
      "DEFAULT_MODE"
    },
    std::vector<std::string>{
      "", "'\\'", "'^'", "'('", "')'", "'{'", "'}'", "'|'", "','", "'ei2pi('", 
      "'eipi('", "'sqrt2'", "'|='", "'+'", "'/'", "", "'\\u2229'", "", "'*'", 
      "", "'\\u2297'", "'-'", "'\\u222A'"
    },
    std::vector<std::string>{
      "", "", "", "", "", "", "", "", "", "", "", "", "", "ADD", "DIV", 
      "DIGITS", "INTERSECTION", "KET", "MUL", "NAME", "PROD", "SUB", "UNION", 
      "WS"
    }
  );
  static const int32_t serializedATNSegment[] = {
  	4,0,23,126,6,-1,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,
  	6,2,7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,2,11,7,11,2,12,7,12,2,13,7,13,2,14,
  	7,14,2,15,7,15,2,16,7,16,2,17,7,17,2,18,7,18,2,19,7,19,2,20,7,20,2,21,
  	7,21,2,22,7,22,1,0,1,0,1,1,1,1,1,2,1,2,1,3,1,3,1,4,1,4,1,5,1,5,1,6,1,
  	6,1,7,1,7,1,8,1,8,1,8,1,8,1,8,1,8,1,8,1,9,1,9,1,9,1,9,1,9,1,9,1,10,1,
  	10,1,10,1,10,1,10,1,10,1,11,1,11,1,11,1,12,1,12,1,13,1,13,1,14,4,14,91,
  	8,14,11,14,12,14,92,1,15,1,15,1,16,1,16,4,16,99,8,16,11,16,12,16,100,
  	1,16,1,16,1,17,1,17,1,18,1,18,5,18,109,8,18,10,18,12,18,112,9,18,1,19,
  	1,19,1,20,1,20,1,21,1,21,1,22,4,22,121,8,22,11,22,12,22,122,1,22,1,22,
  	0,0,23,1,1,3,2,5,3,7,4,9,5,11,6,13,7,15,8,17,9,19,10,21,11,23,12,25,13,
  	27,14,29,15,31,16,33,17,35,18,37,19,39,20,41,21,43,22,45,23,1,0,6,1,0,
  	48,57,5,0,39,39,42,42,48,49,65,90,97,122,2,0,62,62,10217,10217,2,0,65,
  	90,97,122,3,0,48,57,65,90,97,122,3,0,9,10,13,13,32,32,129,0,1,1,0,0,0,
  	0,3,1,0,0,0,0,5,1,0,0,0,0,7,1,0,0,0,0,9,1,0,0,0,0,11,1,0,0,0,0,13,1,0,
  	0,0,0,15,1,0,0,0,0,17,1,0,0,0,0,19,1,0,0,0,0,21,1,0,0,0,0,23,1,0,0,0,
  	0,25,1,0,0,0,0,27,1,0,0,0,0,29,1,0,0,0,0,31,1,0,0,0,0,33,1,0,0,0,0,35,
  	1,0,0,0,0,37,1,0,0,0,0,39,1,0,0,0,0,41,1,0,0,0,0,43,1,0,0,0,0,45,1,0,
  	0,0,1,47,1,0,0,0,3,49,1,0,0,0,5,51,1,0,0,0,7,53,1,0,0,0,9,55,1,0,0,0,
  	11,57,1,0,0,0,13,59,1,0,0,0,15,61,1,0,0,0,17,63,1,0,0,0,19,70,1,0,0,0,
  	21,76,1,0,0,0,23,82,1,0,0,0,25,85,1,0,0,0,27,87,1,0,0,0,29,90,1,0,0,0,
  	31,94,1,0,0,0,33,96,1,0,0,0,35,104,1,0,0,0,37,106,1,0,0,0,39,113,1,0,
  	0,0,41,115,1,0,0,0,43,117,1,0,0,0,45,120,1,0,0,0,47,48,5,92,0,0,48,2,
  	1,0,0,0,49,50,5,94,0,0,50,4,1,0,0,0,51,52,5,40,0,0,52,6,1,0,0,0,53,54,
  	5,41,0,0,54,8,1,0,0,0,55,56,5,123,0,0,56,10,1,0,0,0,57,58,5,125,0,0,58,
  	12,1,0,0,0,59,60,5,124,0,0,60,14,1,0,0,0,61,62,5,44,0,0,62,16,1,0,0,0,
  	63,64,5,101,0,0,64,65,5,105,0,0,65,66,5,50,0,0,66,67,5,112,0,0,67,68,
  	5,105,0,0,68,69,5,40,0,0,69,18,1,0,0,0,70,71,5,101,0,0,71,72,5,105,0,
  	0,72,73,5,112,0,0,73,74,5,105,0,0,74,75,5,40,0,0,75,20,1,0,0,0,76,77,
  	5,115,0,0,77,78,5,113,0,0,78,79,5,114,0,0,79,80,5,116,0,0,80,81,5,50,
  	0,0,81,22,1,0,0,0,82,83,5,124,0,0,83,84,5,61,0,0,84,24,1,0,0,0,85,86,
  	5,43,0,0,86,26,1,0,0,0,87,88,5,47,0,0,88,28,1,0,0,0,89,91,7,0,0,0,90,
  	89,1,0,0,0,91,92,1,0,0,0,92,90,1,0,0,0,92,93,1,0,0,0,93,30,1,0,0,0,94,
  	95,5,8745,0,0,95,32,1,0,0,0,96,98,5,124,0,0,97,99,7,1,0,0,98,97,1,0,0,
  	0,99,100,1,0,0,0,100,98,1,0,0,0,100,101,1,0,0,0,101,102,1,0,0,0,102,103,
  	7,2,0,0,103,34,1,0,0,0,104,105,5,42,0,0,105,36,1,0,0,0,106,110,7,3,0,
  	0,107,109,7,4,0,0,108,107,1,0,0,0,109,112,1,0,0,0,110,108,1,0,0,0,110,
  	111,1,0,0,0,111,38,1,0,0,0,112,110,1,0,0,0,113,114,5,8855,0,0,114,40,
  	1,0,0,0,115,116,5,45,0,0,116,42,1,0,0,0,117,118,5,8746,0,0,118,44,1,0,
  	0,0,119,121,7,5,0,0,120,119,1,0,0,0,121,122,1,0,0,0,122,120,1,0,0,0,122,
  	123,1,0,0,0,123,124,1,0,0,0,124,125,6,22,0,0,125,46,1,0,0,0,5,0,92,100,
  	110,122,1,6,0,0
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
  return "ExtendedDirac.g4";
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




void ExtendedDiracLexer::initialize() {
#if ANTLR4_USE_THREAD_LOCAL_CACHE
  extendeddiraclexerLexerInitialize();
#else
  ::antlr4::internal::call_once(extendeddiraclexerLexerOnceFlag, extendeddiraclexerLexerInitialize);
#endif
}
