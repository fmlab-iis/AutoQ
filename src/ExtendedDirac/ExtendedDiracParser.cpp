
// Generated from src/ExtendedDirac/ExtendedDiracParser.g4 by ANTLR 4.13.2


#include "ExtendedDiracParserListener.h"
#include "ExtendedDiracParserVisitor.h"

#include "ExtendedDiracParser.h"


using namespace antlrcpp;

using namespace antlr4;

namespace {

struct ExtendedDiracParserStaticData final {
  ExtendedDiracParserStaticData(std::vector<std::string> ruleNames,
                        std::vector<std::string> literalNames,
                        std::vector<std::string> symbolicNames)
      : ruleNames(std::move(ruleNames)), literalNames(std::move(literalNames)),
        symbolicNames(std::move(symbolicNames)),
        vocabulary(this->literalNames, this->symbolicNames) {}

  ExtendedDiracParserStaticData(const ExtendedDiracParserStaticData&) = delete;
  ExtendedDiracParserStaticData(ExtendedDiracParserStaticData&&) = delete;
  ExtendedDiracParserStaticData& operator=(const ExtendedDiracParserStaticData&) = delete;
  ExtendedDiracParserStaticData& operator=(ExtendedDiracParserStaticData&&) = delete;

  std::vector<antlr4::dfa::DFA> decisionToDFA;
  antlr4::atn::PredictionContextCache sharedContextCache;
  const std::vector<std::string> ruleNames;
  const std::vector<std::string> literalNames;
  const std::vector<std::string> symbolicNames;
  const antlr4::dfa::Vocabulary vocabulary;
  antlr4::atn::SerializedATNView serializedATN;
  std::unique_ptr<antlr4::atn::ATN> atn;
};

::antlr4::internal::OnceFlag extendeddiracparserParserOnceFlag;
#if ANTLR4_USE_THREAD_LOCAL_CACHE
static thread_local
#endif
std::unique_ptr<ExtendedDiracParserStaticData> extendeddiracparserParserStaticData = nullptr;

void extendeddiracparserParserInitialize() {
#if ANTLR4_USE_THREAD_LOCAL_CACHE
  if (extendeddiracparserParserStaticData != nullptr) {
    return;
  }
#else
  assert(extendeddiracparserParserStaticData == nullptr);
#endif
  auto staticData = std::make_unique<ExtendedDiracParserStaticData>(
    std::vector<std::string>{
      "expr", "tset", "scset", "set", "diracs", "dirac", "term", "complex", 
      "varcons", "varcon", "eq", "ineq", "predicate"
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
  	4,1,30,231,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,6,2,
  	7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,2,11,7,11,2,12,7,12,1,0,1,0,1,0,1,0,1,
  	0,3,0,32,8,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,3,1,41,8,1,1,1,1,1,1,1,5,1,46,
  	8,1,10,1,12,1,49,9,1,1,2,1,2,1,2,1,2,1,2,1,2,5,2,57,8,2,10,2,12,2,60,
  	9,2,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,3,3,73,8,3,1,3,1,3,1,
  	3,5,3,78,8,3,10,3,12,3,81,9,3,1,4,1,4,1,4,1,4,1,4,1,4,5,4,89,8,4,10,4,
  	12,4,92,9,4,1,5,1,5,1,5,1,5,1,5,1,5,5,5,100,8,5,10,5,12,5,103,9,5,1,6,
  	3,6,106,8,6,1,6,1,6,1,6,1,6,3,6,112,8,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,
  	6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,3,6,131,8,6,1,7,1,7,1,7,1,7,1,7,
  	1,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,3,7,147,8,7,1,7,1,7,1,7,1,7,1,7,1,
  	7,1,7,1,7,1,7,1,7,5,7,159,8,7,10,7,12,7,162,9,7,1,8,1,8,1,8,1,8,1,8,1,
  	8,5,8,170,8,8,10,8,12,8,173,9,8,1,9,1,9,1,9,1,9,1,9,1,9,1,9,1,9,3,9,183,
  	8,9,1,10,1,10,1,10,1,10,1,11,1,11,1,11,1,11,1,12,1,12,1,12,1,12,1,12,
  	1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,1,12,
  	1,12,1,12,1,12,1,12,1,12,1,12,3,12,218,8,12,1,12,1,12,1,12,1,12,1,12,
  	1,12,5,12,226,8,12,10,12,12,12,229,9,12,1,12,0,8,2,4,6,8,10,14,16,24,
  	13,0,2,4,6,8,10,12,14,16,18,20,22,24,0,3,2,0,9,9,14,14,2,0,1,1,21,21,
  	2,0,5,5,9,9,248,0,31,1,0,0,0,2,40,1,0,0,0,4,50,1,0,0,0,6,72,1,0,0,0,8,
  	82,1,0,0,0,10,93,1,0,0,0,12,130,1,0,0,0,14,146,1,0,0,0,16,163,1,0,0,0,
  	18,182,1,0,0,0,20,184,1,0,0,0,22,188,1,0,0,0,24,217,1,0,0,0,26,32,3,2,
  	1,0,27,28,3,2,1,0,28,29,5,19,0,0,29,30,3,2,1,0,30,32,1,0,0,0,31,26,1,
  	0,0,0,31,27,1,0,0,0,32,1,1,0,0,0,33,34,6,1,-1,0,34,41,3,4,2,0,35,36,3,
  	6,3,0,36,37,5,12,0,0,37,38,5,20,0,0,38,39,4,1,0,1,39,41,1,0,0,0,40,33,
  	1,0,0,0,40,35,1,0,0,0,41,47,1,0,0,0,42,43,10,1,0,0,43,44,7,0,0,0,44,46,
  	3,2,1,2,45,42,1,0,0,0,46,49,1,0,0,0,47,45,1,0,0,0,47,48,1,0,0,0,48,3,
  	1,0,0,0,49,47,1,0,0,0,50,51,6,2,-1,0,51,52,3,6,3,0,52,58,1,0,0,0,53,54,
  	10,2,0,0,54,55,5,18,0,0,55,57,3,6,3,0,56,53,1,0,0,0,57,60,1,0,0,0,58,
  	56,1,0,0,0,58,59,1,0,0,0,59,5,1,0,0,0,60,58,1,0,0,0,61,62,6,3,-1,0,62,
  	63,5,8,0,0,63,64,3,8,4,0,64,65,5,17,0,0,65,73,1,0,0,0,66,67,5,8,0,0,67,
  	68,3,8,4,0,68,69,5,4,0,0,69,70,3,16,8,0,70,71,5,17,0,0,71,73,1,0,0,0,
  	72,61,1,0,0,0,72,66,1,0,0,0,73,79,1,0,0,0,74,75,10,3,0,0,75,76,5,23,0,
  	0,76,78,3,6,3,4,77,74,1,0,0,0,78,81,1,0,0,0,79,77,1,0,0,0,79,80,1,0,0,
  	0,80,7,1,0,0,0,81,79,1,0,0,0,82,83,6,4,-1,0,83,84,3,10,5,0,84,90,1,0,
  	0,0,85,86,10,1,0,0,86,87,5,3,0,0,87,89,3,10,5,0,88,85,1,0,0,0,89,92,1,
  	0,0,0,90,88,1,0,0,0,90,91,1,0,0,0,91,9,1,0,0,0,92,90,1,0,0,0,93,94,6,
  	5,-1,0,94,95,3,12,6,0,95,101,1,0,0,0,96,97,10,1,0,0,97,98,7,1,0,0,98,
  	100,3,12,6,0,99,96,1,0,0,0,100,103,1,0,0,0,101,99,1,0,0,0,101,102,1,0,
  	0,0,102,11,1,0,0,0,103,101,1,0,0,0,104,106,3,14,7,0,105,104,1,0,0,0,105,
  	106,1,0,0,0,106,107,1,0,0,0,107,108,5,2,0,0,108,109,5,20,0,0,109,131,
  	5,15,0,0,110,112,3,14,7,0,111,110,1,0,0,0,111,112,1,0,0,0,112,113,1,0,
  	0,0,113,114,5,22,0,0,114,115,3,16,8,0,115,116,5,2,0,0,116,117,5,20,0,
  	0,117,118,5,15,0,0,118,131,1,0,0,0,119,120,5,21,0,0,120,121,5,2,0,0,121,
  	122,5,20,0,0,122,131,5,15,0,0,123,124,5,21,0,0,124,125,5,22,0,0,125,126,
  	3,16,8,0,126,127,5,2,0,0,127,128,5,20,0,0,128,129,5,15,0,0,129,131,1,
  	0,0,0,130,105,1,0,0,0,130,111,1,0,0,0,130,119,1,0,0,0,130,123,1,0,0,0,
  	131,13,1,0,0,0,132,133,6,7,-1,0,133,134,5,21,0,0,134,147,3,14,7,6,135,
  	136,5,7,0,0,136,137,3,14,7,0,137,138,5,16,0,0,138,147,1,0,0,0,139,140,
  	5,20,0,0,140,141,5,7,0,0,141,142,3,14,7,0,142,143,5,16,0,0,143,144,4,
  	7,6,1,144,147,1,0,0,0,145,147,5,20,0,0,146,132,1,0,0,0,146,135,1,0,0,
  	0,146,139,1,0,0,0,146,145,1,0,0,0,147,160,1,0,0,0,148,149,10,5,0,0,149,
  	150,7,2,0,0,150,159,3,14,7,6,151,152,10,4,0,0,152,153,7,1,0,0,153,159,
  	3,14,7,5,154,155,10,7,0,0,155,156,5,12,0,0,156,157,5,20,0,0,157,159,4,
  	7,10,1,158,148,1,0,0,0,158,151,1,0,0,0,158,154,1,0,0,0,159,162,1,0,0,
  	0,160,158,1,0,0,0,160,161,1,0,0,0,161,15,1,0,0,0,162,160,1,0,0,0,163,
  	164,6,8,-1,0,164,165,3,18,9,0,165,171,1,0,0,0,166,167,10,1,0,0,167,168,
  	5,3,0,0,168,170,3,18,9,0,169,166,1,0,0,0,170,173,1,0,0,0,171,169,1,0,
  	0,0,171,172,1,0,0,0,172,17,1,0,0,0,173,171,1,0,0,0,174,175,5,2,0,0,175,
  	176,5,20,0,0,176,177,5,2,0,0,177,178,5,6,0,0,178,179,5,20,0,0,179,183,
  	4,9,12,1,180,183,3,20,10,0,181,183,3,22,11,0,182,174,1,0,0,0,182,180,
  	1,0,0,0,182,181,1,0,0,0,183,19,1,0,0,0,184,185,3,14,7,0,185,186,5,6,0,
  	0,186,187,3,14,7,0,187,21,1,0,0,0,188,189,3,14,7,0,189,190,5,10,0,0,190,
  	191,3,14,7,0,191,23,1,0,0,0,192,193,6,12,-1,0,193,218,3,20,10,0,194,218,
  	3,22,11,0,195,196,3,14,7,0,196,197,5,28,0,0,197,198,3,14,7,0,198,218,
  	1,0,0,0,199,200,3,14,7,0,200,201,5,29,0,0,201,202,3,14,7,0,202,218,1,
  	0,0,0,203,204,3,14,7,0,204,205,5,15,0,0,205,206,3,14,7,0,206,218,1,0,
  	0,0,207,208,3,14,7,0,208,209,5,30,0,0,209,210,3,14,7,0,210,218,1,0,0,
  	0,211,212,5,27,0,0,212,218,3,24,12,4,213,214,5,7,0,0,214,215,3,24,12,
  	0,215,216,5,16,0,0,216,218,1,0,0,0,217,192,1,0,0,0,217,194,1,0,0,0,217,
  	195,1,0,0,0,217,199,1,0,0,0,217,203,1,0,0,0,217,207,1,0,0,0,217,211,1,
  	0,0,0,217,213,1,0,0,0,218,227,1,0,0,0,219,220,10,3,0,0,220,221,5,25,0,
  	0,221,226,3,24,12,4,222,223,10,2,0,0,223,224,5,26,0,0,224,226,3,24,12,
  	3,225,219,1,0,0,0,225,222,1,0,0,0,226,229,1,0,0,0,227,225,1,0,0,0,227,
  	228,1,0,0,0,228,25,1,0,0,0,229,227,1,0,0,0,19,31,40,47,58,72,79,90,101,
  	105,111,130,146,158,160,171,182,217,225,227
  };
  staticData->serializedATN = antlr4::atn::SerializedATNView(serializedATNSegment, sizeof(serializedATNSegment) / sizeof(serializedATNSegment[0]));

  antlr4::atn::ATNDeserializer deserializer;
  staticData->atn = deserializer.deserialize(staticData->serializedATN);

  const size_t count = staticData->atn->getNumberOfDecisions();
  staticData->decisionToDFA.reserve(count);
  for (size_t i = 0; i < count; i++) { 
    staticData->decisionToDFA.emplace_back(staticData->atn->getDecisionState(i), i);
  }
  extendeddiracparserParserStaticData = std::move(staticData);
}

}

ExtendedDiracParser::ExtendedDiracParser(TokenStream *input) : ExtendedDiracParser(input, antlr4::atn::ParserATNSimulatorOptions()) {}

ExtendedDiracParser::ExtendedDiracParser(TokenStream *input, const antlr4::atn::ParserATNSimulatorOptions &options) : Parser(input) {
  ExtendedDiracParser::initialize();
  _interpreter = new atn::ParserATNSimulator(this, *extendeddiracparserParserStaticData->atn, extendeddiracparserParserStaticData->decisionToDFA, extendeddiracparserParserStaticData->sharedContextCache, options);
}

ExtendedDiracParser::~ExtendedDiracParser() {
  delete _interpreter;
}

const atn::ATN& ExtendedDiracParser::getATN() const {
  return *extendeddiracparserParserStaticData->atn;
}

std::string ExtendedDiracParser::getGrammarFileName() const {
  return "ExtendedDiracParser.g4";
}

const std::vector<std::string>& ExtendedDiracParser::getRuleNames() const {
  return extendeddiracparserParserStaticData->ruleNames;
}

const dfa::Vocabulary& ExtendedDiracParser::getVocabulary() const {
  return extendeddiracparserParserStaticData->vocabulary;
}

antlr4::atn::SerializedATNView ExtendedDiracParser::getSerializedATN() const {
  return extendeddiracparserParserStaticData->serializedATN;
}


//----------------- ExprContext ------------------------------------------------------------------

ExtendedDiracParser::ExprContext::ExprContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<ExtendedDiracParser::TsetContext *> ExtendedDiracParser::ExprContext::tset() {
  return getRuleContexts<ExtendedDiracParser::TsetContext>();
}

ExtendedDiracParser::TsetContext* ExtendedDiracParser::ExprContext::tset(size_t i) {
  return getRuleContext<ExtendedDiracParser::TsetContext>(i);
}

tree::TerminalNode* ExtendedDiracParser::ExprContext::SETMINUS() {
  return getToken(ExtendedDiracParser::SETMINUS, 0);
}


size_t ExtendedDiracParser::ExprContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleExpr;
}

void ExtendedDiracParser::ExprContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterExpr(this);
}

void ExtendedDiracParser::ExprContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitExpr(this);
}


std::any ExtendedDiracParser::ExprContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitExpr(this);
  else
    return visitor->visitChildren(this);
}

ExtendedDiracParser::ExprContext* ExtendedDiracParser::expr() {
  ExprContext *_localctx = _tracker.createInstance<ExprContext>(_ctx, getState());
  enterRule(_localctx, 0, ExtendedDiracParser::RuleExpr);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(31);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 0, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(26);
      tset(0);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(27);
      tset(0);
      setState(28);
      match(ExtendedDiracParser::SETMINUS);
      setState(29);
      tset(0);
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- TsetContext ------------------------------------------------------------------

ExtendedDiracParser::TsetContext::TsetContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

ExtendedDiracParser::ScsetContext* ExtendedDiracParser::TsetContext::scset() {
  return getRuleContext<ExtendedDiracParser::ScsetContext>(0);
}

ExtendedDiracParser::SetContext* ExtendedDiracParser::TsetContext::set() {
  return getRuleContext<ExtendedDiracParser::SetContext>(0);
}

tree::TerminalNode* ExtendedDiracParser::TsetContext::POWER() {
  return getToken(ExtendedDiracParser::POWER, 0);
}

tree::TerminalNode* ExtendedDiracParser::TsetContext::STR() {
  return getToken(ExtendedDiracParser::STR, 0);
}

std::vector<ExtendedDiracParser::TsetContext *> ExtendedDiracParser::TsetContext::tset() {
  return getRuleContexts<ExtendedDiracParser::TsetContext>();
}

ExtendedDiracParser::TsetContext* ExtendedDiracParser::TsetContext::tset(size_t i) {
  return getRuleContext<ExtendedDiracParser::TsetContext>(i);
}

tree::TerminalNode* ExtendedDiracParser::TsetContext::MUL() {
  return getToken(ExtendedDiracParser::MUL, 0);
}

tree::TerminalNode* ExtendedDiracParser::TsetContext::PROD() {
  return getToken(ExtendedDiracParser::PROD, 0);
}


size_t ExtendedDiracParser::TsetContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleTset;
}

void ExtendedDiracParser::TsetContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterTset(this);
}

void ExtendedDiracParser::TsetContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitTset(this);
}


std::any ExtendedDiracParser::TsetContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitTset(this);
  else
    return visitor->visitChildren(this);
}


ExtendedDiracParser::TsetContext* ExtendedDiracParser::tset() {
   return tset(0);
}

ExtendedDiracParser::TsetContext* ExtendedDiracParser::tset(int precedence) {
  ParserRuleContext *parentContext = _ctx;
  size_t parentState = getState();
  ExtendedDiracParser::TsetContext *_localctx = _tracker.createInstance<TsetContext>(_ctx, parentState);
  ExtendedDiracParser::TsetContext *previousContext = _localctx;
  (void)previousContext; // Silence compiler, in case the context is not used by generated code.
  size_t startState = 2;
  enterRecursionRule(_localctx, 2, ExtendedDiracParser::RuleTset, precedence);

    size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    unrollRecursionContexts(parentContext);
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(40);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 1, _ctx)) {
    case 1: {
      setState(34);
      scset(0);
      break;
    }

    case 2: {
      setState(35);
      set(0);
      setState(36);
      match(ExtendedDiracParser::POWER);
      setState(37);
      antlrcpp::downCast<TsetContext *>(_localctx)->N = match(ExtendedDiracParser::STR);
      setState(38);

      if (!( isNonZero((antlrcpp::downCast<TsetContext *>(_localctx)->N != nullptr ? antlrcpp::downCast<TsetContext *>(_localctx)->N->getText() : "")) )) throw FailedPredicateException(this, " isNonZero($N.text) ");
      break;
    }

    default:
      break;
    }
    _ctx->stop = _input->LT(-1);
    setState(47);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 2, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<TsetContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleTset);
        setState(42);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(43);
        _la = _input->LA(1);
        if (!(_la == ExtendedDiracParser::MUL

        || _la == ExtendedDiracParser::PROD)) {
        _errHandler->recoverInline(this);
        }
        else {
          _errHandler->reportMatch(this);
          consume();
        }
        setState(44);
        tset(2); 
      }
      setState(49);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 2, _ctx);
    }
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }
  return _localctx;
}

//----------------- ScsetContext ------------------------------------------------------------------

ExtendedDiracParser::ScsetContext::ScsetContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

ExtendedDiracParser::SetContext* ExtendedDiracParser::ScsetContext::set() {
  return getRuleContext<ExtendedDiracParser::SetContext>(0);
}

ExtendedDiracParser::ScsetContext* ExtendedDiracParser::ScsetContext::scset() {
  return getRuleContext<ExtendedDiracParser::ScsetContext>(0);
}

tree::TerminalNode* ExtendedDiracParser::ScsetContext::SEMICOLON() {
  return getToken(ExtendedDiracParser::SEMICOLON, 0);
}


size_t ExtendedDiracParser::ScsetContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleScset;
}

void ExtendedDiracParser::ScsetContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterScset(this);
}

void ExtendedDiracParser::ScsetContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitScset(this);
}


std::any ExtendedDiracParser::ScsetContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitScset(this);
  else
    return visitor->visitChildren(this);
}


ExtendedDiracParser::ScsetContext* ExtendedDiracParser::scset() {
   return scset(0);
}

ExtendedDiracParser::ScsetContext* ExtendedDiracParser::scset(int precedence) {
  ParserRuleContext *parentContext = _ctx;
  size_t parentState = getState();
  ExtendedDiracParser::ScsetContext *_localctx = _tracker.createInstance<ScsetContext>(_ctx, parentState);
  ExtendedDiracParser::ScsetContext *previousContext = _localctx;
  (void)previousContext; // Silence compiler, in case the context is not used by generated code.
  size_t startState = 4;
  enterRecursionRule(_localctx, 4, ExtendedDiracParser::RuleScset, precedence);

    

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    unrollRecursionContexts(parentContext);
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(51);
    set(0);
    _ctx->stop = _input->LT(-1);
    setState(58);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 3, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<ScsetContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleScset);
        setState(53);

        if (!(precpred(_ctx, 2))) throw FailedPredicateException(this, "precpred(_ctx, 2)");
        setState(54);
        match(ExtendedDiracParser::SEMICOLON);
        setState(55);
        set(0); 
      }
      setState(60);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 3, _ctx);
    }
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }
  return _localctx;
}

//----------------- SetContext ------------------------------------------------------------------

ExtendedDiracParser::SetContext::SetContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* ExtendedDiracParser::SetContext::LEFT_BRACE() {
  return getToken(ExtendedDiracParser::LEFT_BRACE, 0);
}

ExtendedDiracParser::DiracsContext* ExtendedDiracParser::SetContext::diracs() {
  return getRuleContext<ExtendedDiracParser::DiracsContext>(0);
}

tree::TerminalNode* ExtendedDiracParser::SetContext::RIGHT_BRACE() {
  return getToken(ExtendedDiracParser::RIGHT_BRACE, 0);
}

tree::TerminalNode* ExtendedDiracParser::SetContext::COLON() {
  return getToken(ExtendedDiracParser::COLON, 0);
}

ExtendedDiracParser::VarconsContext* ExtendedDiracParser::SetContext::varcons() {
  return getRuleContext<ExtendedDiracParser::VarconsContext>(0);
}

std::vector<ExtendedDiracParser::SetContext *> ExtendedDiracParser::SetContext::set() {
  return getRuleContexts<ExtendedDiracParser::SetContext>();
}

ExtendedDiracParser::SetContext* ExtendedDiracParser::SetContext::set(size_t i) {
  return getRuleContext<ExtendedDiracParser::SetContext>(i);
}

tree::TerminalNode* ExtendedDiracParser::SetContext::UNION() {
  return getToken(ExtendedDiracParser::UNION, 0);
}


size_t ExtendedDiracParser::SetContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleSet;
}

void ExtendedDiracParser::SetContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSet(this);
}

void ExtendedDiracParser::SetContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSet(this);
}


std::any ExtendedDiracParser::SetContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitSet(this);
  else
    return visitor->visitChildren(this);
}


ExtendedDiracParser::SetContext* ExtendedDiracParser::set() {
   return set(0);
}

ExtendedDiracParser::SetContext* ExtendedDiracParser::set(int precedence) {
  ParserRuleContext *parentContext = _ctx;
  size_t parentState = getState();
  ExtendedDiracParser::SetContext *_localctx = _tracker.createInstance<SetContext>(_ctx, parentState);
  ExtendedDiracParser::SetContext *previousContext = _localctx;
  (void)previousContext; // Silence compiler, in case the context is not used by generated code.
  size_t startState = 6;
  enterRecursionRule(_localctx, 6, ExtendedDiracParser::RuleSet, precedence);

    

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    unrollRecursionContexts(parentContext);
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(72);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 4, _ctx)) {
    case 1: {
      setState(62);
      match(ExtendedDiracParser::LEFT_BRACE);
      setState(63);
      diracs(0);
      setState(64);
      match(ExtendedDiracParser::RIGHT_BRACE);
      break;
    }

    case 2: {
      setState(66);
      match(ExtendedDiracParser::LEFT_BRACE);
      setState(67);
      diracs(0);
      setState(68);
      match(ExtendedDiracParser::COLON);
      setState(69);
      varcons(0);
      setState(70);
      match(ExtendedDiracParser::RIGHT_BRACE);
      break;
    }

    default:
      break;
    }
    _ctx->stop = _input->LT(-1);
    setState(79);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 5, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<SetContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleSet);
        setState(74);

        if (!(precpred(_ctx, 3))) throw FailedPredicateException(this, "precpred(_ctx, 3)");
        setState(75);
        match(ExtendedDiracParser::UNION);
        setState(76);
        set(4); 
      }
      setState(81);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 5, _ctx);
    }
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }
  return _localctx;
}

//----------------- DiracsContext ------------------------------------------------------------------

ExtendedDiracParser::DiracsContext::DiracsContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

ExtendedDiracParser::DiracContext* ExtendedDiracParser::DiracsContext::dirac() {
  return getRuleContext<ExtendedDiracParser::DiracContext>(0);
}

ExtendedDiracParser::DiracsContext* ExtendedDiracParser::DiracsContext::diracs() {
  return getRuleContext<ExtendedDiracParser::DiracsContext>(0);
}

tree::TerminalNode* ExtendedDiracParser::DiracsContext::COMMA() {
  return getToken(ExtendedDiracParser::COMMA, 0);
}


size_t ExtendedDiracParser::DiracsContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleDiracs;
}

void ExtendedDiracParser::DiracsContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDiracs(this);
}

void ExtendedDiracParser::DiracsContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDiracs(this);
}


std::any ExtendedDiracParser::DiracsContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitDiracs(this);
  else
    return visitor->visitChildren(this);
}


ExtendedDiracParser::DiracsContext* ExtendedDiracParser::diracs() {
   return diracs(0);
}

ExtendedDiracParser::DiracsContext* ExtendedDiracParser::diracs(int precedence) {
  ParserRuleContext *parentContext = _ctx;
  size_t parentState = getState();
  ExtendedDiracParser::DiracsContext *_localctx = _tracker.createInstance<DiracsContext>(_ctx, parentState);
  ExtendedDiracParser::DiracsContext *previousContext = _localctx;
  (void)previousContext; // Silence compiler, in case the context is not used by generated code.
  size_t startState = 8;
  enterRecursionRule(_localctx, 8, ExtendedDiracParser::RuleDiracs, precedence);

    

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    unrollRecursionContexts(parentContext);
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(83);
    dirac(0);
    _ctx->stop = _input->LT(-1);
    setState(90);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 6, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<DiracsContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleDiracs);
        setState(85);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(86);
        match(ExtendedDiracParser::COMMA);
        setState(87);
        dirac(0); 
      }
      setState(92);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 6, _ctx);
    }
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }
  return _localctx;
}

//----------------- DiracContext ------------------------------------------------------------------

ExtendedDiracParser::DiracContext::DiracContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

ExtendedDiracParser::TermContext* ExtendedDiracParser::DiracContext::term() {
  return getRuleContext<ExtendedDiracParser::TermContext>(0);
}

ExtendedDiracParser::DiracContext* ExtendedDiracParser::DiracContext::dirac() {
  return getRuleContext<ExtendedDiracParser::DiracContext>(0);
}

tree::TerminalNode* ExtendedDiracParser::DiracContext::ADD() {
  return getToken(ExtendedDiracParser::ADD, 0);
}

tree::TerminalNode* ExtendedDiracParser::DiracContext::SUB() {
  return getToken(ExtendedDiracParser::SUB, 0);
}


size_t ExtendedDiracParser::DiracContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleDirac;
}

void ExtendedDiracParser::DiracContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDirac(this);
}

void ExtendedDiracParser::DiracContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDirac(this);
}


std::any ExtendedDiracParser::DiracContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitDirac(this);
  else
    return visitor->visitChildren(this);
}


ExtendedDiracParser::DiracContext* ExtendedDiracParser::dirac() {
   return dirac(0);
}

ExtendedDiracParser::DiracContext* ExtendedDiracParser::dirac(int precedence) {
  ParserRuleContext *parentContext = _ctx;
  size_t parentState = getState();
  ExtendedDiracParser::DiracContext *_localctx = _tracker.createInstance<DiracContext>(_ctx, parentState);
  ExtendedDiracParser::DiracContext *previousContext = _localctx;
  (void)previousContext; // Silence compiler, in case the context is not used by generated code.
  size_t startState = 10;
  enterRecursionRule(_localctx, 10, ExtendedDiracParser::RuleDirac, precedence);

    size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    unrollRecursionContexts(parentContext);
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(94);
    term();
    _ctx->stop = _input->LT(-1);
    setState(101);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 7, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<DiracContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleDirac);
        setState(96);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(97);
        _la = _input->LA(1);
        if (!(_la == ExtendedDiracParser::ADD

        || _la == ExtendedDiracParser::SUB)) {
        _errHandler->recoverInline(this);
        }
        else {
          _errHandler->reportMatch(this);
          consume();
        }
        setState(98);
        term(); 
      }
      setState(103);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 7, _ctx);
    }
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }
  return _localctx;
}

//----------------- TermContext ------------------------------------------------------------------

ExtendedDiracParser::TermContext::TermContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* ExtendedDiracParser::TermContext::BAR() {
  return getToken(ExtendedDiracParser::BAR, 0);
}

tree::TerminalNode* ExtendedDiracParser::TermContext::RIGHT_ANGLE_BRACKET() {
  return getToken(ExtendedDiracParser::RIGHT_ANGLE_BRACKET, 0);
}

tree::TerminalNode* ExtendedDiracParser::TermContext::STR() {
  return getToken(ExtendedDiracParser::STR, 0);
}

ExtendedDiracParser::ComplexContext* ExtendedDiracParser::TermContext::complex() {
  return getRuleContext<ExtendedDiracParser::ComplexContext>(0);
}

tree::TerminalNode* ExtendedDiracParser::TermContext::SUM() {
  return getToken(ExtendedDiracParser::SUM, 0);
}

ExtendedDiracParser::VarconsContext* ExtendedDiracParser::TermContext::varcons() {
  return getRuleContext<ExtendedDiracParser::VarconsContext>(0);
}

tree::TerminalNode* ExtendedDiracParser::TermContext::SUB() {
  return getToken(ExtendedDiracParser::SUB, 0);
}


size_t ExtendedDiracParser::TermContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleTerm;
}

void ExtendedDiracParser::TermContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterTerm(this);
}

void ExtendedDiracParser::TermContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitTerm(this);
}


std::any ExtendedDiracParser::TermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitTerm(this);
  else
    return visitor->visitChildren(this);
}

ExtendedDiracParser::TermContext* ExtendedDiracParser::term() {
  TermContext *_localctx = _tracker.createInstance<TermContext>(_ctx, getState());
  enterRule(_localctx, 12, ExtendedDiracParser::RuleTerm);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(130);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 10, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(105);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & 3145856) != 0)) {
        setState(104);
        complex(0);
      }
      setState(107);
      match(ExtendedDiracParser::BAR);
      setState(108);
      antlrcpp::downCast<TermContext *>(_localctx)->VStr = match(ExtendedDiracParser::STR);
      setState(109);
      match(ExtendedDiracParser::RIGHT_ANGLE_BRACKET);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(111);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & 3145856) != 0)) {
        setState(110);
        complex(0);
      }
      setState(113);
      match(ExtendedDiracParser::SUM);
      setState(114);
      varcons(0);
      setState(115);
      match(ExtendedDiracParser::BAR);
      setState(116);
      antlrcpp::downCast<TermContext *>(_localctx)->VStr = match(ExtendedDiracParser::STR);
      setState(117);
      match(ExtendedDiracParser::RIGHT_ANGLE_BRACKET);
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(119);
      match(ExtendedDiracParser::SUB);
      setState(120);
      match(ExtendedDiracParser::BAR);
      setState(121);
      antlrcpp::downCast<TermContext *>(_localctx)->VStr = match(ExtendedDiracParser::STR);
      setState(122);
      match(ExtendedDiracParser::RIGHT_ANGLE_BRACKET);
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(123);
      match(ExtendedDiracParser::SUB);
      setState(124);
      match(ExtendedDiracParser::SUM);
      setState(125);
      varcons(0);
      setState(126);
      match(ExtendedDiracParser::BAR);
      setState(127);
      antlrcpp::downCast<TermContext *>(_localctx)->VStr = match(ExtendedDiracParser::STR);
      setState(128);
      match(ExtendedDiracParser::RIGHT_ANGLE_BRACKET);
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- ComplexContext ------------------------------------------------------------------

ExtendedDiracParser::ComplexContext::ComplexContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<ExtendedDiracParser::ComplexContext *> ExtendedDiracParser::ComplexContext::complex() {
  return getRuleContexts<ExtendedDiracParser::ComplexContext>();
}

ExtendedDiracParser::ComplexContext* ExtendedDiracParser::ComplexContext::complex(size_t i) {
  return getRuleContext<ExtendedDiracParser::ComplexContext>(i);
}

tree::TerminalNode* ExtendedDiracParser::ComplexContext::SUB() {
  return getToken(ExtendedDiracParser::SUB, 0);
}

tree::TerminalNode* ExtendedDiracParser::ComplexContext::LEFT_PARENTHESIS() {
  return getToken(ExtendedDiracParser::LEFT_PARENTHESIS, 0);
}

tree::TerminalNode* ExtendedDiracParser::ComplexContext::RIGHT_PARENTHESIS() {
  return getToken(ExtendedDiracParser::RIGHT_PARENTHESIS, 0);
}

tree::TerminalNode* ExtendedDiracParser::ComplexContext::STR() {
  return getToken(ExtendedDiracParser::STR, 0);
}

tree::TerminalNode* ExtendedDiracParser::ComplexContext::MUL() {
  return getToken(ExtendedDiracParser::MUL, 0);
}

tree::TerminalNode* ExtendedDiracParser::ComplexContext::DIV() {
  return getToken(ExtendedDiracParser::DIV, 0);
}

tree::TerminalNode* ExtendedDiracParser::ComplexContext::ADD() {
  return getToken(ExtendedDiracParser::ADD, 0);
}

tree::TerminalNode* ExtendedDiracParser::ComplexContext::POWER() {
  return getToken(ExtendedDiracParser::POWER, 0);
}


size_t ExtendedDiracParser::ComplexContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleComplex;
}

void ExtendedDiracParser::ComplexContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterComplex(this);
}

void ExtendedDiracParser::ComplexContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitComplex(this);
}


std::any ExtendedDiracParser::ComplexContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitComplex(this);
  else
    return visitor->visitChildren(this);
}


ExtendedDiracParser::ComplexContext* ExtendedDiracParser::complex() {
   return complex(0);
}

ExtendedDiracParser::ComplexContext* ExtendedDiracParser::complex(int precedence) {
  ParserRuleContext *parentContext = _ctx;
  size_t parentState = getState();
  ExtendedDiracParser::ComplexContext *_localctx = _tracker.createInstance<ComplexContext>(_ctx, parentState);
  ExtendedDiracParser::ComplexContext *previousContext = _localctx;
  (void)previousContext; // Silence compiler, in case the context is not used by generated code.
  size_t startState = 14;
  enterRecursionRule(_localctx, 14, ExtendedDiracParser::RuleComplex, precedence);

    size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    unrollRecursionContexts(parentContext);
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(146);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 11, _ctx)) {
    case 1: {
      setState(133);
      antlrcpp::downCast<ComplexContext *>(_localctx)->sub = match(ExtendedDiracParser::SUB);
      setState(134);
      complex(6);
      break;
    }

    case 2: {
      setState(135);
      match(ExtendedDiracParser::LEFT_PARENTHESIS);
      setState(136);
      complex(0);
      setState(137);
      match(ExtendedDiracParser::RIGHT_PARENTHESIS);
      break;
    }

    case 3: {
      setState(139);
      antlrcpp::downCast<ComplexContext *>(_localctx)->func = match(ExtendedDiracParser::STR);
      setState(140);
      match(ExtendedDiracParser::LEFT_PARENTHESIS);
      setState(141);
      complex(0);
      setState(142);
      match(ExtendedDiracParser::RIGHT_PARENTHESIS);
      setState(143);

      if (!( (antlrcpp::downCast<ComplexContext *>(_localctx)->func != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->func->getText() : "") == "real" || (antlrcpp::downCast<ComplexContext *>(_localctx)->func != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->func->getText() : "") == "imag" || (antlrcpp::downCast<ComplexContext *>(_localctx)->func != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->func->getText() : "") == "eipi" || (antlrcpp::downCast<ComplexContext *>(_localctx)->func != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->func->getText() : "") == "ei2pi" )) throw FailedPredicateException(this, " $func.text == \"real\" || $func.text == \"imag\" || $func.text == \"eipi\" || $func.text == \"ei2pi\" ");
      break;
    }

    case 4: {
      setState(145);
      antlrcpp::downCast<ComplexContext *>(_localctx)->var = match(ExtendedDiracParser::STR);
      break;
    }

    default:
      break;
    }
    _ctx->stop = _input->LT(-1);
    setState(160);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 13, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        setState(158);
        _errHandler->sync(this);
        switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 12, _ctx)) {
        case 1: {
          _localctx = _tracker.createInstance<ComplexContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleComplex);
          setState(148);

          if (!(precpred(_ctx, 5))) throw FailedPredicateException(this, "precpred(_ctx, 5)");
          setState(149);
          antlrcpp::downCast<ComplexContext *>(_localctx)->op = _input->LT(1);
          _la = _input->LA(1);
          if (!(_la == ExtendedDiracParser::DIV

          || _la == ExtendedDiracParser::MUL)) {
            antlrcpp::downCast<ComplexContext *>(_localctx)->op = _errHandler->recoverInline(this);
          }
          else {
            _errHandler->reportMatch(this);
            consume();
          }
          setState(150);
          complex(6);
          break;
        }

        case 2: {
          _localctx = _tracker.createInstance<ComplexContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleComplex);
          setState(151);

          if (!(precpred(_ctx, 4))) throw FailedPredicateException(this, "precpred(_ctx, 4)");
          setState(152);
          antlrcpp::downCast<ComplexContext *>(_localctx)->op = _input->LT(1);
          _la = _input->LA(1);
          if (!(_la == ExtendedDiracParser::ADD

          || _la == ExtendedDiracParser::SUB)) {
            antlrcpp::downCast<ComplexContext *>(_localctx)->op = _errHandler->recoverInline(this);
          }
          else {
            _errHandler->reportMatch(this);
            consume();
          }
          setState(153);
          complex(5);
          break;
        }

        case 3: {
          _localctx = _tracker.createInstance<ComplexContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleComplex);
          setState(154);

          if (!(precpred(_ctx, 7))) throw FailedPredicateException(this, "precpred(_ctx, 7)");
          setState(155);
          match(ExtendedDiracParser::POWER);
          setState(156);
          antlrcpp::downCast<ComplexContext *>(_localctx)->n = match(ExtendedDiracParser::STR);
          setState(157);

          if (!( areAllDigits((antlrcpp::downCast<ComplexContext *>(_localctx)->n != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->n->getText() : "")) )) throw FailedPredicateException(this, " areAllDigits($n.text) ");
          break;
        }

        default:
          break;
        } 
      }
      setState(162);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 13, _ctx);
    }
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }
  return _localctx;
}

//----------------- VarconsContext ------------------------------------------------------------------

ExtendedDiracParser::VarconsContext::VarconsContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

ExtendedDiracParser::VarconContext* ExtendedDiracParser::VarconsContext::varcon() {
  return getRuleContext<ExtendedDiracParser::VarconContext>(0);
}

ExtendedDiracParser::VarconsContext* ExtendedDiracParser::VarconsContext::varcons() {
  return getRuleContext<ExtendedDiracParser::VarconsContext>(0);
}

tree::TerminalNode* ExtendedDiracParser::VarconsContext::COMMA() {
  return getToken(ExtendedDiracParser::COMMA, 0);
}


size_t ExtendedDiracParser::VarconsContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleVarcons;
}

void ExtendedDiracParser::VarconsContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterVarcons(this);
}

void ExtendedDiracParser::VarconsContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitVarcons(this);
}


std::any ExtendedDiracParser::VarconsContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitVarcons(this);
  else
    return visitor->visitChildren(this);
}


ExtendedDiracParser::VarconsContext* ExtendedDiracParser::varcons() {
   return varcons(0);
}

ExtendedDiracParser::VarconsContext* ExtendedDiracParser::varcons(int precedence) {
  ParserRuleContext *parentContext = _ctx;
  size_t parentState = getState();
  ExtendedDiracParser::VarconsContext *_localctx = _tracker.createInstance<VarconsContext>(_ctx, parentState);
  ExtendedDiracParser::VarconsContext *previousContext = _localctx;
  (void)previousContext; // Silence compiler, in case the context is not used by generated code.
  size_t startState = 16;
  enterRecursionRule(_localctx, 16, ExtendedDiracParser::RuleVarcons, precedence);

    

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    unrollRecursionContexts(parentContext);
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(164);
    varcon();
    _ctx->stop = _input->LT(-1);
    setState(171);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 14, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<VarconsContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleVarcons);
        setState(166);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(167);
        match(ExtendedDiracParser::COMMA);
        setState(168);
        varcon(); 
      }
      setState(173);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 14, _ctx);
    }
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }
  return _localctx;
}

//----------------- VarconContext ------------------------------------------------------------------

ExtendedDiracParser::VarconContext::VarconContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<tree::TerminalNode *> ExtendedDiracParser::VarconContext::BAR() {
  return getTokens(ExtendedDiracParser::BAR);
}

tree::TerminalNode* ExtendedDiracParser::VarconContext::BAR(size_t i) {
  return getToken(ExtendedDiracParser::BAR, i);
}

tree::TerminalNode* ExtendedDiracParser::VarconContext::EQ() {
  return getToken(ExtendedDiracParser::EQ, 0);
}

std::vector<tree::TerminalNode *> ExtendedDiracParser::VarconContext::STR() {
  return getTokens(ExtendedDiracParser::STR);
}

tree::TerminalNode* ExtendedDiracParser::VarconContext::STR(size_t i) {
  return getToken(ExtendedDiracParser::STR, i);
}

ExtendedDiracParser::EqContext* ExtendedDiracParser::VarconContext::eq() {
  return getRuleContext<ExtendedDiracParser::EqContext>(0);
}

ExtendedDiracParser::IneqContext* ExtendedDiracParser::VarconContext::ineq() {
  return getRuleContext<ExtendedDiracParser::IneqContext>(0);
}


size_t ExtendedDiracParser::VarconContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleVarcon;
}

void ExtendedDiracParser::VarconContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterVarcon(this);
}

void ExtendedDiracParser::VarconContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitVarcon(this);
}


std::any ExtendedDiracParser::VarconContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitVarcon(this);
  else
    return visitor->visitChildren(this);
}

ExtendedDiracParser::VarconContext* ExtendedDiracParser::varcon() {
  VarconContext *_localctx = _tracker.createInstance<VarconContext>(_ctx, getState());
  enterRule(_localctx, 18, ExtendedDiracParser::RuleVarcon);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(182);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 15, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(174);
      match(ExtendedDiracParser::BAR);
      setState(175);
      antlrcpp::downCast<VarconContext *>(_localctx)->V = match(ExtendedDiracParser::STR);
      setState(176);
      match(ExtendedDiracParser::BAR);
      setState(177);
      match(ExtendedDiracParser::EQ);
      setState(178);
      antlrcpp::downCast<VarconContext *>(_localctx)->N = match(ExtendedDiracParser::STR);
      setState(179);

      if (!( isALowercaseLetter((antlrcpp::downCast<VarconContext *>(_localctx)->V != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->V->getText() : "")) && isNonZero((antlrcpp::downCast<VarconContext *>(_localctx)->N != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->N->getText() : "")) )) throw FailedPredicateException(this, " isALowercaseLetter($V.text) && isNonZero($N.text) ");
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(180);
      eq();
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(181);
      ineq();
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- EqContext ------------------------------------------------------------------

ExtendedDiracParser::EqContext::EqContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<ExtendedDiracParser::ComplexContext *> ExtendedDiracParser::EqContext::complex() {
  return getRuleContexts<ExtendedDiracParser::ComplexContext>();
}

ExtendedDiracParser::ComplexContext* ExtendedDiracParser::EqContext::complex(size_t i) {
  return getRuleContext<ExtendedDiracParser::ComplexContext>(i);
}

tree::TerminalNode* ExtendedDiracParser::EqContext::EQ() {
  return getToken(ExtendedDiracParser::EQ, 0);
}


size_t ExtendedDiracParser::EqContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleEq;
}

void ExtendedDiracParser::EqContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEq(this);
}

void ExtendedDiracParser::EqContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEq(this);
}


std::any ExtendedDiracParser::EqContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitEq(this);
  else
    return visitor->visitChildren(this);
}

ExtendedDiracParser::EqContext* ExtendedDiracParser::eq() {
  EqContext *_localctx = _tracker.createInstance<EqContext>(_ctx, getState());
  enterRule(_localctx, 20, ExtendedDiracParser::RuleEq);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(184);
    complex(0);
    setState(185);
    match(ExtendedDiracParser::EQ);
    setState(186);
    complex(0);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- IneqContext ------------------------------------------------------------------

ExtendedDiracParser::IneqContext::IneqContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<ExtendedDiracParser::ComplexContext *> ExtendedDiracParser::IneqContext::complex() {
  return getRuleContexts<ExtendedDiracParser::ComplexContext>();
}

ExtendedDiracParser::ComplexContext* ExtendedDiracParser::IneqContext::complex(size_t i) {
  return getRuleContext<ExtendedDiracParser::ComplexContext>(i);
}

tree::TerminalNode* ExtendedDiracParser::IneqContext::NE() {
  return getToken(ExtendedDiracParser::NE, 0);
}


size_t ExtendedDiracParser::IneqContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleIneq;
}

void ExtendedDiracParser::IneqContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterIneq(this);
}

void ExtendedDiracParser::IneqContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitIneq(this);
}


std::any ExtendedDiracParser::IneqContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitIneq(this);
  else
    return visitor->visitChildren(this);
}

ExtendedDiracParser::IneqContext* ExtendedDiracParser::ineq() {
  IneqContext *_localctx = _tracker.createInstance<IneqContext>(_ctx, getState());
  enterRule(_localctx, 22, ExtendedDiracParser::RuleIneq);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(188);
    complex(0);
    setState(189);
    match(ExtendedDiracParser::NE);
    setState(190);
    complex(0);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- PredicateContext ------------------------------------------------------------------

ExtendedDiracParser::PredicateContext::PredicateContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

ExtendedDiracParser::EqContext* ExtendedDiracParser::PredicateContext::eq() {
  return getRuleContext<ExtendedDiracParser::EqContext>(0);
}

ExtendedDiracParser::IneqContext* ExtendedDiracParser::PredicateContext::ineq() {
  return getRuleContext<ExtendedDiracParser::IneqContext>(0);
}

std::vector<ExtendedDiracParser::ComplexContext *> ExtendedDiracParser::PredicateContext::complex() {
  return getRuleContexts<ExtendedDiracParser::ComplexContext>();
}

ExtendedDiracParser::ComplexContext* ExtendedDiracParser::PredicateContext::complex(size_t i) {
  return getRuleContext<ExtendedDiracParser::ComplexContext>(i);
}

tree::TerminalNode* ExtendedDiracParser::PredicateContext::LESS_THAN() {
  return getToken(ExtendedDiracParser::LESS_THAN, 0);
}

tree::TerminalNode* ExtendedDiracParser::PredicateContext::LESS_EQUAL() {
  return getToken(ExtendedDiracParser::LESS_EQUAL, 0);
}

tree::TerminalNode* ExtendedDiracParser::PredicateContext::RIGHT_ANGLE_BRACKET() {
  return getToken(ExtendedDiracParser::RIGHT_ANGLE_BRACKET, 0);
}

tree::TerminalNode* ExtendedDiracParser::PredicateContext::GREATER_EQUAL() {
  return getToken(ExtendedDiracParser::GREATER_EQUAL, 0);
}

tree::TerminalNode* ExtendedDiracParser::PredicateContext::LOGICAL_NOT() {
  return getToken(ExtendedDiracParser::LOGICAL_NOT, 0);
}

std::vector<ExtendedDiracParser::PredicateContext *> ExtendedDiracParser::PredicateContext::predicate() {
  return getRuleContexts<ExtendedDiracParser::PredicateContext>();
}

ExtendedDiracParser::PredicateContext* ExtendedDiracParser::PredicateContext::predicate(size_t i) {
  return getRuleContext<ExtendedDiracParser::PredicateContext>(i);
}

tree::TerminalNode* ExtendedDiracParser::PredicateContext::LEFT_PARENTHESIS() {
  return getToken(ExtendedDiracParser::LEFT_PARENTHESIS, 0);
}

tree::TerminalNode* ExtendedDiracParser::PredicateContext::RIGHT_PARENTHESIS() {
  return getToken(ExtendedDiracParser::RIGHT_PARENTHESIS, 0);
}

tree::TerminalNode* ExtendedDiracParser::PredicateContext::LOGICAL_AND() {
  return getToken(ExtendedDiracParser::LOGICAL_AND, 0);
}

tree::TerminalNode* ExtendedDiracParser::PredicateContext::LOGICAL_OR() {
  return getToken(ExtendedDiracParser::LOGICAL_OR, 0);
}


size_t ExtendedDiracParser::PredicateContext::getRuleIndex() const {
  return ExtendedDiracParser::RulePredicate;
}

void ExtendedDiracParser::PredicateContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterPredicate(this);
}

void ExtendedDiracParser::PredicateContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitPredicate(this);
}


std::any ExtendedDiracParser::PredicateContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitPredicate(this);
  else
    return visitor->visitChildren(this);
}


ExtendedDiracParser::PredicateContext* ExtendedDiracParser::predicate() {
   return predicate(0);
}

ExtendedDiracParser::PredicateContext* ExtendedDiracParser::predicate(int precedence) {
  ParserRuleContext *parentContext = _ctx;
  size_t parentState = getState();
  ExtendedDiracParser::PredicateContext *_localctx = _tracker.createInstance<PredicateContext>(_ctx, parentState);
  ExtendedDiracParser::PredicateContext *previousContext = _localctx;
  (void)previousContext; // Silence compiler, in case the context is not used by generated code.
  size_t startState = 24;
  enterRecursionRule(_localctx, 24, ExtendedDiracParser::RulePredicate, precedence);

    

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    unrollRecursionContexts(parentContext);
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(217);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 16, _ctx)) {
    case 1: {
      setState(193);
      eq();
      break;
    }

    case 2: {
      setState(194);
      ineq();
      break;
    }

    case 3: {
      setState(195);
      complex(0);
      setState(196);
      match(ExtendedDiracParser::LESS_THAN);
      setState(197);
      complex(0);
      break;
    }

    case 4: {
      setState(199);
      complex(0);
      setState(200);
      match(ExtendedDiracParser::LESS_EQUAL);
      setState(201);
      complex(0);
      break;
    }

    case 5: {
      setState(203);
      complex(0);
      setState(204);
      match(ExtendedDiracParser::RIGHT_ANGLE_BRACKET);
      setState(205);
      complex(0);
      break;
    }

    case 6: {
      setState(207);
      complex(0);
      setState(208);
      match(ExtendedDiracParser::GREATER_EQUAL);
      setState(209);
      complex(0);
      break;
    }

    case 7: {
      setState(211);
      match(ExtendedDiracParser::LOGICAL_NOT);
      setState(212);
      predicate(4);
      break;
    }

    case 8: {
      setState(213);
      match(ExtendedDiracParser::LEFT_PARENTHESIS);
      setState(214);
      predicate(0);
      setState(215);
      match(ExtendedDiracParser::RIGHT_PARENTHESIS);
      break;
    }

    default:
      break;
    }
    _ctx->stop = _input->LT(-1);
    setState(227);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 18, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        setState(225);
        _errHandler->sync(this);
        switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 17, _ctx)) {
        case 1: {
          _localctx = _tracker.createInstance<PredicateContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RulePredicate);
          setState(219);

          if (!(precpred(_ctx, 3))) throw FailedPredicateException(this, "precpred(_ctx, 3)");
          setState(220);
          match(ExtendedDiracParser::LOGICAL_AND);
          setState(221);
          predicate(4);
          break;
        }

        case 2: {
          _localctx = _tracker.createInstance<PredicateContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RulePredicate);
          setState(222);

          if (!(precpred(_ctx, 2))) throw FailedPredicateException(this, "precpred(_ctx, 2)");
          setState(223);
          match(ExtendedDiracParser::LOGICAL_OR);
          setState(224);
          predicate(3);
          break;
        }

        default:
          break;
        } 
      }
      setState(229);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 18, _ctx);
    }
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }
  return _localctx;
}

bool ExtendedDiracParser::sempred(RuleContext *context, size_t ruleIndex, size_t predicateIndex) {
  switch (ruleIndex) {
    case 1: return tsetSempred(antlrcpp::downCast<TsetContext *>(context), predicateIndex);
    case 2: return scsetSempred(antlrcpp::downCast<ScsetContext *>(context), predicateIndex);
    case 3: return setSempred(antlrcpp::downCast<SetContext *>(context), predicateIndex);
    case 4: return diracsSempred(antlrcpp::downCast<DiracsContext *>(context), predicateIndex);
    case 5: return diracSempred(antlrcpp::downCast<DiracContext *>(context), predicateIndex);
    case 7: return complexSempred(antlrcpp::downCast<ComplexContext *>(context), predicateIndex);
    case 8: return varconsSempred(antlrcpp::downCast<VarconsContext *>(context), predicateIndex);
    case 9: return varconSempred(antlrcpp::downCast<VarconContext *>(context), predicateIndex);
    case 12: return predicateSempred(antlrcpp::downCast<PredicateContext *>(context), predicateIndex);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::tsetSempred(TsetContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 0: return  isNonZero((antlrcpp::downCast<TsetContext *>(_localctx)->N != nullptr ? antlrcpp::downCast<TsetContext *>(_localctx)->N->getText() : "")) ;
    case 1: return precpred(_ctx, 1);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::scsetSempred(ScsetContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 2: return precpred(_ctx, 2);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::setSempred(SetContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 3: return precpred(_ctx, 3);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::diracsSempred(DiracsContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 4: return precpred(_ctx, 1);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::diracSempred(DiracContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 5: return precpred(_ctx, 1);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::complexSempred(ComplexContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 6: return  (antlrcpp::downCast<ComplexContext *>(_localctx)->func != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->func->getText() : "") == "real" || (antlrcpp::downCast<ComplexContext *>(_localctx)->func != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->func->getText() : "") == "imag" || (antlrcpp::downCast<ComplexContext *>(_localctx)->func != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->func->getText() : "") == "eipi" || (antlrcpp::downCast<ComplexContext *>(_localctx)->func != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->func->getText() : "") == "ei2pi" ;
    case 7: return precpred(_ctx, 5);
    case 8: return precpred(_ctx, 4);
    case 9: return precpred(_ctx, 7);
    case 10: return  areAllDigits((antlrcpp::downCast<ComplexContext *>(_localctx)->n != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->n->getText() : "")) ;

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::varconsSempred(VarconsContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 11: return precpred(_ctx, 1);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::varconSempred(VarconContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 12: return  isALowercaseLetter((antlrcpp::downCast<VarconContext *>(_localctx)->V != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->V->getText() : "")) && isNonZero((antlrcpp::downCast<VarconContext *>(_localctx)->N != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->N->getText() : "")) ;

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::predicateSempred(PredicateContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 13: return precpred(_ctx, 3);
    case 14: return precpred(_ctx, 2);

  default:
    break;
  }
  return true;
}

void ExtendedDiracParser::initialize() {
#if ANTLR4_USE_THREAD_LOCAL_CACHE
  extendeddiracparserParserInitialize();
#else
  ::antlr4::internal::call_once(extendeddiracparserParserOnceFlag, extendeddiracparserParserInitialize);
#endif
}
