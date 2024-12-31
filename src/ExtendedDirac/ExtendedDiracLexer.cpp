
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
      "ADD", "BAR", "COMMA", "DIV", "DIGITS", "EI2PI", "EIPI", "EQ", "INTERSECTION", 
      "KET", "LEFT_BRACKET", "LEFT_CURLY_BRACKET", "MUL", "NEWLINES", "POWER", 
      "PROD", "RIGHT_BRACKET", "RIGHT_CURLY_BRACKET", "SUB", "SETMINUS", 
      "SQRT2", "UNION", "WHERE", "WS", "NAME"
    },
    std::vector<std::string>{
      "DEFAULT_TOKEN_CHANNEL", "HIDDEN"
    },
    std::vector<std::string>{
      "DEFAULT_MODE"
    },
    std::vector<std::string>{
      "", "'+'", "'|'", "','", "'/'", "", "'ei2pi'", "'eipi'", "'='", "'\\u2229'", 
      "", "'('", "'{'", "'*'", "", "'^'", "'\\u2297'", "')'", "'}'", "'-'", 
      "'\\'", "'sqrt2'", "'\\u222A'", "'where'"
    },
    std::vector<std::string>{
      "", "ADD", "BAR", "COMMA", "DIV", "DIGITS", "EI2PI", "EIPI", "EQ", 
      "INTERSECTION", "KET", "LEFT_BRACKET", "LEFT_CURLY_BRACKET", "MUL", 
      "NEWLINES", "POWER", "PROD", "RIGHT_BRACKET", "RIGHT_CURLY_BRACKET", 
      "SUB", "SETMINUS", "SQRT2", "UNION", "WHERE", "WS", "NAME"
    }
  );
  static const int32_t serializedATNSegment[] = {
  	4,0,25,142,6,-1,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,
  	6,2,7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,2,11,7,11,2,12,7,12,2,13,7,13,2,14,
  	7,14,2,15,7,15,2,16,7,16,2,17,7,17,2,18,7,18,2,19,7,19,2,20,7,20,2,21,
  	7,21,2,22,7,22,2,23,7,23,2,24,7,24,1,0,1,0,1,1,1,1,1,2,1,2,1,3,1,3,1,
  	4,4,4,61,8,4,11,4,12,4,62,1,5,1,5,1,5,1,5,1,5,1,5,1,6,1,6,1,6,1,6,1,6,
  	1,7,1,7,1,8,1,8,1,9,1,9,4,9,82,8,9,11,9,12,9,83,1,9,1,9,1,10,1,10,1,11,
  	1,11,1,12,1,12,1,13,4,13,95,8,13,11,13,12,13,96,1,13,1,13,1,14,1,14,1,
  	15,1,15,1,16,1,16,1,17,1,17,1,18,1,18,1,19,1,19,1,20,1,20,1,20,1,20,1,
  	20,1,20,1,21,1,21,1,22,1,22,1,22,1,22,1,22,1,22,1,22,1,22,1,23,4,23,130,
  	8,23,11,23,12,23,131,1,23,1,23,1,24,1,24,5,24,138,8,24,10,24,12,24,141,
  	9,24,0,0,25,1,1,3,2,5,3,7,4,9,5,11,6,13,7,15,8,17,9,19,10,21,11,23,12,
  	25,13,27,14,29,15,31,16,33,17,35,18,37,19,39,20,41,21,43,22,45,23,47,
  	24,49,25,1,0,7,1,0,48,57,5,0,39,39,42,42,48,49,65,90,97,122,2,0,62,62,
  	10217,10217,2,0,10,10,13,13,2,0,9,9,32,32,2,0,65,90,97,122,3,0,48,57,
  	65,90,97,122,146,0,1,1,0,0,0,0,3,1,0,0,0,0,5,1,0,0,0,0,7,1,0,0,0,0,9,
  	1,0,0,0,0,11,1,0,0,0,0,13,1,0,0,0,0,15,1,0,0,0,0,17,1,0,0,0,0,19,1,0,
  	0,0,0,21,1,0,0,0,0,23,1,0,0,0,0,25,1,0,0,0,0,27,1,0,0,0,0,29,1,0,0,0,
  	0,31,1,0,0,0,0,33,1,0,0,0,0,35,1,0,0,0,0,37,1,0,0,0,0,39,1,0,0,0,0,41,
  	1,0,0,0,0,43,1,0,0,0,0,45,1,0,0,0,0,47,1,0,0,0,0,49,1,0,0,0,1,51,1,0,
  	0,0,3,53,1,0,0,0,5,55,1,0,0,0,7,57,1,0,0,0,9,60,1,0,0,0,11,64,1,0,0,0,
  	13,70,1,0,0,0,15,75,1,0,0,0,17,77,1,0,0,0,19,79,1,0,0,0,21,87,1,0,0,0,
  	23,89,1,0,0,0,25,91,1,0,0,0,27,94,1,0,0,0,29,100,1,0,0,0,31,102,1,0,0,
  	0,33,104,1,0,0,0,35,106,1,0,0,0,37,108,1,0,0,0,39,110,1,0,0,0,41,112,
  	1,0,0,0,43,118,1,0,0,0,45,120,1,0,0,0,47,129,1,0,0,0,49,135,1,0,0,0,51,
  	52,5,43,0,0,52,2,1,0,0,0,53,54,5,124,0,0,54,4,1,0,0,0,55,56,5,44,0,0,
  	56,6,1,0,0,0,57,58,5,47,0,0,58,8,1,0,0,0,59,61,7,0,0,0,60,59,1,0,0,0,
  	61,62,1,0,0,0,62,60,1,0,0,0,62,63,1,0,0,0,63,10,1,0,0,0,64,65,5,101,0,
  	0,65,66,5,105,0,0,66,67,5,50,0,0,67,68,5,112,0,0,68,69,5,105,0,0,69,12,
  	1,0,0,0,70,71,5,101,0,0,71,72,5,105,0,0,72,73,5,112,0,0,73,74,5,105,0,
  	0,74,14,1,0,0,0,75,76,5,61,0,0,76,16,1,0,0,0,77,78,5,8745,0,0,78,18,1,
  	0,0,0,79,81,3,3,1,0,80,82,7,1,0,0,81,80,1,0,0,0,82,83,1,0,0,0,83,81,1,
  	0,0,0,83,84,1,0,0,0,84,85,1,0,0,0,85,86,7,2,0,0,86,20,1,0,0,0,87,88,5,
  	40,0,0,88,22,1,0,0,0,89,90,5,123,0,0,90,24,1,0,0,0,91,92,5,42,0,0,92,
  	26,1,0,0,0,93,95,7,3,0,0,94,93,1,0,0,0,95,96,1,0,0,0,96,94,1,0,0,0,96,
  	97,1,0,0,0,97,98,1,0,0,0,98,99,6,13,0,0,99,28,1,0,0,0,100,101,5,94,0,
  	0,101,30,1,0,0,0,102,103,5,8855,0,0,103,32,1,0,0,0,104,105,5,41,0,0,105,
  	34,1,0,0,0,106,107,5,125,0,0,107,36,1,0,0,0,108,109,5,45,0,0,109,38,1,
  	0,0,0,110,111,5,92,0,0,111,40,1,0,0,0,112,113,5,115,0,0,113,114,5,113,
  	0,0,114,115,5,114,0,0,115,116,5,116,0,0,116,117,5,50,0,0,117,42,1,0,0,
  	0,118,119,5,8746,0,0,119,44,1,0,0,0,120,121,5,119,0,0,121,122,5,104,0,
  	0,122,123,5,101,0,0,123,124,5,114,0,0,124,125,5,101,0,0,125,126,1,0,0,
  	0,126,127,6,22,1,0,127,46,1,0,0,0,128,130,7,4,0,0,129,128,1,0,0,0,130,
  	131,1,0,0,0,131,129,1,0,0,0,131,132,1,0,0,0,132,133,1,0,0,0,133,134,6,
  	23,2,0,134,48,1,0,0,0,135,139,7,5,0,0,136,138,7,6,0,0,137,136,1,0,0,0,
  	138,141,1,0,0,0,139,137,1,0,0,0,139,140,1,0,0,0,140,50,1,0,0,0,141,139,
  	1,0,0,0,6,0,62,83,96,131,139,3,1,13,0,1,22,1,6,0,0
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
    case 13: NEWLINESAction(antlrcpp::downCast<antlr4::RuleContext *>(context), actionIndex); break;
    case 22: WHEREAction(antlrcpp::downCast<antlr4::RuleContext *>(context), actionIndex); break;

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

void ExtendedDiracLexer::WHEREAction(antlr4::RuleContext *context, size_t actionIndex) {
  switch (actionIndex) {
    case 1:  skipNewline = false;  break;

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
