
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
      "angle", "varcons", "varcon", "eq", "ineq", "predicate"
    },
    std::vector<std::string>{
      "", "'+'", "'|'", "','", "':'", "'/'", "'='", "'('", "'{'", "'*'", 
      "'\\u2260'", "", "'^'", "'''", "'\\u2297'", "", "')'", "'}'", "';'", 
      "'\\'", "", "'-'", "", "'\\u222A'", "", "", "", "", "'<'"
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
  	4,1,30,247,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,6,2,
  	7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,2,11,7,11,2,12,7,12,2,13,7,13,1,0,1,0,
  	1,0,1,0,1,0,3,0,34,8,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,3,1,43,8,1,1,1,1,1,
  	1,1,5,1,48,8,1,10,1,12,1,51,9,1,1,2,1,2,1,2,1,2,1,2,1,2,5,2,59,8,2,10,
  	2,12,2,62,9,2,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,3,3,75,8,3,
  	1,3,1,3,1,3,5,3,80,8,3,10,3,12,3,83,9,3,1,4,1,4,1,4,1,4,1,4,1,4,5,4,91,
  	8,4,10,4,12,4,94,9,4,1,5,1,5,1,5,1,5,1,5,1,5,5,5,102,8,5,10,5,12,5,105,
  	9,5,1,6,3,6,108,8,6,1,6,1,6,1,6,1,6,3,6,114,8,6,1,6,1,6,1,6,1,6,1,6,1,
  	6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,3,6,133,8,6,1,7,1,7,1,7,
  	1,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,3,7,149,8,7,1,7,1,7,1,7,1,
  	7,1,7,1,7,1,7,1,7,1,7,1,7,5,7,161,8,7,10,7,12,7,164,9,7,1,8,3,8,167,8,
  	8,1,8,1,8,1,8,1,8,1,8,3,8,174,8,8,1,8,1,8,3,8,178,8,8,1,9,1,9,1,9,1,9,
  	1,9,1,9,5,9,186,8,9,10,9,12,9,189,9,9,1,10,1,10,1,10,1,10,1,10,1,10,1,
  	10,1,10,3,10,199,8,10,1,11,1,11,1,11,1,11,1,12,1,12,1,12,1,12,1,13,1,
  	13,1,13,1,13,1,13,1,13,1,13,1,13,1,13,1,13,1,13,1,13,1,13,1,13,1,13,1,
  	13,1,13,1,13,1,13,1,13,1,13,1,13,1,13,1,13,1,13,3,13,234,8,13,1,13,1,
  	13,1,13,1,13,1,13,1,13,5,13,242,8,13,10,13,12,13,245,9,13,1,13,0,8,2,
  	4,6,8,10,14,18,26,14,0,2,4,6,8,10,12,14,16,18,20,22,24,26,0,2,2,0,1,1,
  	21,21,2,0,5,5,9,9,266,0,33,1,0,0,0,2,42,1,0,0,0,4,52,1,0,0,0,6,74,1,0,
  	0,0,8,84,1,0,0,0,10,95,1,0,0,0,12,132,1,0,0,0,14,148,1,0,0,0,16,177,1,
  	0,0,0,18,179,1,0,0,0,20,198,1,0,0,0,22,200,1,0,0,0,24,204,1,0,0,0,26,
  	233,1,0,0,0,28,34,3,2,1,0,29,30,3,2,1,0,30,31,5,19,0,0,31,32,3,2,1,0,
  	32,34,1,0,0,0,33,28,1,0,0,0,33,29,1,0,0,0,34,1,1,0,0,0,35,36,6,1,-1,0,
  	36,43,3,4,2,0,37,38,3,6,3,0,38,39,5,12,0,0,39,40,5,20,0,0,40,41,4,1,0,
  	1,41,43,1,0,0,0,42,35,1,0,0,0,42,37,1,0,0,0,43,49,1,0,0,0,44,45,10,1,
  	0,0,45,46,5,14,0,0,46,48,3,2,1,2,47,44,1,0,0,0,48,51,1,0,0,0,49,47,1,
  	0,0,0,49,50,1,0,0,0,50,3,1,0,0,0,51,49,1,0,0,0,52,53,6,2,-1,0,53,54,3,
  	6,3,0,54,60,1,0,0,0,55,56,10,2,0,0,56,57,5,18,0,0,57,59,3,6,3,0,58,55,
  	1,0,0,0,59,62,1,0,0,0,60,58,1,0,0,0,60,61,1,0,0,0,61,5,1,0,0,0,62,60,
  	1,0,0,0,63,64,6,3,-1,0,64,65,5,8,0,0,65,66,3,8,4,0,66,67,5,17,0,0,67,
  	75,1,0,0,0,68,69,5,8,0,0,69,70,3,8,4,0,70,71,5,4,0,0,71,72,3,18,9,0,72,
  	73,5,17,0,0,73,75,1,0,0,0,74,63,1,0,0,0,74,68,1,0,0,0,75,81,1,0,0,0,76,
  	77,10,3,0,0,77,78,5,23,0,0,78,80,3,6,3,4,79,76,1,0,0,0,80,83,1,0,0,0,
  	81,79,1,0,0,0,81,82,1,0,0,0,82,7,1,0,0,0,83,81,1,0,0,0,84,85,6,4,-1,0,
  	85,86,3,10,5,0,86,92,1,0,0,0,87,88,10,1,0,0,88,89,5,3,0,0,89,91,3,10,
  	5,0,90,87,1,0,0,0,91,94,1,0,0,0,92,90,1,0,0,0,92,93,1,0,0,0,93,9,1,0,
  	0,0,94,92,1,0,0,0,95,96,6,5,-1,0,96,97,3,12,6,0,97,103,1,0,0,0,98,99,
  	10,1,0,0,99,100,7,0,0,0,100,102,3,12,6,0,101,98,1,0,0,0,102,105,1,0,0,
  	0,103,101,1,0,0,0,103,104,1,0,0,0,104,11,1,0,0,0,105,103,1,0,0,0,106,
  	108,3,14,7,0,107,106,1,0,0,0,107,108,1,0,0,0,108,109,1,0,0,0,109,110,
  	5,2,0,0,110,111,5,20,0,0,111,133,5,15,0,0,112,114,3,14,7,0,113,112,1,
  	0,0,0,113,114,1,0,0,0,114,115,1,0,0,0,115,116,5,22,0,0,116,117,3,18,9,
  	0,117,118,5,2,0,0,118,119,5,20,0,0,119,120,5,15,0,0,120,133,1,0,0,0,121,
  	122,5,21,0,0,122,123,5,2,0,0,123,124,5,20,0,0,124,133,5,15,0,0,125,126,
  	5,21,0,0,126,127,5,22,0,0,127,128,3,18,9,0,128,129,5,2,0,0,129,130,5,
  	20,0,0,130,131,5,15,0,0,131,133,1,0,0,0,132,107,1,0,0,0,132,113,1,0,0,
  	0,132,121,1,0,0,0,132,125,1,0,0,0,133,13,1,0,0,0,134,135,6,7,-1,0,135,
  	136,5,21,0,0,136,149,3,14,7,6,137,138,5,7,0,0,138,139,3,14,7,0,139,140,
  	5,16,0,0,140,149,1,0,0,0,141,142,5,20,0,0,142,143,5,7,0,0,143,144,3,14,
  	7,0,144,145,5,16,0,0,145,146,4,7,6,1,146,149,1,0,0,0,147,149,5,20,0,0,
  	148,134,1,0,0,0,148,137,1,0,0,0,148,141,1,0,0,0,148,147,1,0,0,0,149,162,
  	1,0,0,0,150,151,10,5,0,0,151,152,7,1,0,0,152,161,3,14,7,6,153,154,10,
  	4,0,0,154,155,7,0,0,0,155,161,3,14,7,5,156,157,10,7,0,0,157,158,5,12,
  	0,0,158,159,5,20,0,0,159,161,4,7,10,1,160,150,1,0,0,0,160,153,1,0,0,0,
  	160,156,1,0,0,0,161,164,1,0,0,0,162,160,1,0,0,0,162,163,1,0,0,0,163,15,
  	1,0,0,0,164,162,1,0,0,0,165,167,5,21,0,0,166,165,1,0,0,0,166,167,1,0,
  	0,0,167,168,1,0,0,0,168,169,5,20,0,0,169,170,5,5,0,0,170,171,5,20,0,0,
  	171,178,4,8,11,1,172,174,5,21,0,0,173,172,1,0,0,0,173,174,1,0,0,0,174,
  	175,1,0,0,0,175,176,5,20,0,0,176,178,4,8,12,1,177,166,1,0,0,0,177,173,
  	1,0,0,0,178,17,1,0,0,0,179,180,6,9,-1,0,180,181,3,20,10,0,181,187,1,0,
  	0,0,182,183,10,1,0,0,183,184,5,3,0,0,184,186,3,20,10,0,185,182,1,0,0,
  	0,186,189,1,0,0,0,187,185,1,0,0,0,187,188,1,0,0,0,188,19,1,0,0,0,189,
  	187,1,0,0,0,190,191,5,2,0,0,191,192,5,20,0,0,192,193,5,2,0,0,193,194,
  	5,6,0,0,194,195,5,20,0,0,195,199,4,10,14,1,196,199,3,22,11,0,197,199,
  	3,24,12,0,198,190,1,0,0,0,198,196,1,0,0,0,198,197,1,0,0,0,199,21,1,0,
  	0,0,200,201,3,14,7,0,201,202,5,6,0,0,202,203,3,14,7,0,203,23,1,0,0,0,
  	204,205,3,14,7,0,205,206,5,10,0,0,206,207,3,14,7,0,207,25,1,0,0,0,208,
  	209,6,13,-1,0,209,234,3,22,11,0,210,234,3,24,12,0,211,212,3,14,7,0,212,
  	213,5,28,0,0,213,214,3,14,7,0,214,234,1,0,0,0,215,216,3,14,7,0,216,217,
  	5,29,0,0,217,218,3,14,7,0,218,234,1,0,0,0,219,220,3,14,7,0,220,221,5,
  	15,0,0,221,222,3,14,7,0,222,234,1,0,0,0,223,224,3,14,7,0,224,225,5,30,
  	0,0,225,226,3,14,7,0,226,234,1,0,0,0,227,228,5,27,0,0,228,234,3,26,13,
  	4,229,230,5,7,0,0,230,231,3,26,13,0,231,232,5,16,0,0,232,234,1,0,0,0,
  	233,208,1,0,0,0,233,210,1,0,0,0,233,211,1,0,0,0,233,215,1,0,0,0,233,219,
  	1,0,0,0,233,223,1,0,0,0,233,227,1,0,0,0,233,229,1,0,0,0,234,243,1,0,0,
  	0,235,236,10,3,0,0,236,237,5,25,0,0,237,242,3,26,13,4,238,239,10,2,0,
  	0,239,240,5,26,0,0,240,242,3,26,13,3,241,235,1,0,0,0,241,238,1,0,0,0,
  	242,245,1,0,0,0,243,241,1,0,0,0,243,244,1,0,0,0,244,27,1,0,0,0,245,243,
  	1,0,0,0,22,33,42,49,60,74,81,92,103,107,113,132,148,160,162,166,173,177,
  	187,198,233,241,243
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
    setState(33);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 0, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(28);
      tset(0);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(29);
      tset(0);
      setState(30);
      match(ExtendedDiracParser::SETMINUS);
      setState(31);
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
    setState(42);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 1, _ctx)) {
    case 1: {
      setState(36);
      scset(0);
      break;
    }

    case 2: {
      setState(37);
      set(0);
      setState(38);
      match(ExtendedDiracParser::POWER);
      setState(39);
      antlrcpp::downCast<TsetContext *>(_localctx)->N = match(ExtendedDiracParser::STR);
      setState(40);

      if (!( isNonZero((antlrcpp::downCast<TsetContext *>(_localctx)->N != nullptr ? antlrcpp::downCast<TsetContext *>(_localctx)->N->getText() : "")) )) throw FailedPredicateException(this, " isNonZero($N.text) ");
      break;
    }

    default:
      break;
    }
    _ctx->stop = _input->LT(-1);
    setState(49);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 2, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<TsetContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleTset);
        setState(44);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(45);
        match(ExtendedDiracParser::PROD);
        setState(46);
        tset(2); 
      }
      setState(51);
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
    setState(53);
    set(0);
    _ctx->stop = _input->LT(-1);
    setState(60);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 3, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<ScsetContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleScset);
        setState(55);

        if (!(precpred(_ctx, 2))) throw FailedPredicateException(this, "precpred(_ctx, 2)");
        setState(56);
        match(ExtendedDiracParser::SEMICOLON);
        setState(57);
        set(0); 
      }
      setState(62);
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
    setState(74);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 4, _ctx)) {
    case 1: {
      setState(64);
      match(ExtendedDiracParser::LEFT_BRACE);
      setState(65);
      diracs(0);
      setState(66);
      match(ExtendedDiracParser::RIGHT_BRACE);
      break;
    }

    case 2: {
      setState(68);
      match(ExtendedDiracParser::LEFT_BRACE);
      setState(69);
      diracs(0);
      setState(70);
      match(ExtendedDiracParser::COLON);
      setState(71);
      varcons(0);
      setState(72);
      match(ExtendedDiracParser::RIGHT_BRACE);
      break;
    }

    default:
      break;
    }
    _ctx->stop = _input->LT(-1);
    setState(81);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 5, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<SetContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleSet);
        setState(76);

        if (!(precpred(_ctx, 3))) throw FailedPredicateException(this, "precpred(_ctx, 3)");
        setState(77);
        match(ExtendedDiracParser::UNION);
        setState(78);
        set(4); 
      }
      setState(83);
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
    setState(85);
    dirac(0);
    _ctx->stop = _input->LT(-1);
    setState(92);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 6, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<DiracsContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleDiracs);
        setState(87);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(88);
        match(ExtendedDiracParser::COMMA);
        setState(89);
        dirac(0); 
      }
      setState(94);
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
    setState(96);
    term();
    _ctx->stop = _input->LT(-1);
    setState(103);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 7, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<DiracContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleDirac);
        setState(98);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(99);
        _la = _input->LA(1);
        if (!(_la == ExtendedDiracParser::ADD

        || _la == ExtendedDiracParser::SUB)) {
        _errHandler->recoverInline(this);
        }
        else {
          _errHandler->reportMatch(this);
          consume();
        }
        setState(100);
        term(); 
      }
      setState(105);
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
    setState(132);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 10, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(107);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & 3145856) != 0)) {
        setState(106);
        complex(0);
      }
      setState(109);
      match(ExtendedDiracParser::BAR);
      setState(110);
      antlrcpp::downCast<TermContext *>(_localctx)->VStr = match(ExtendedDiracParser::STR);
      setState(111);
      match(ExtendedDiracParser::RIGHT_ANGLE_BRACKET);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(113);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & 3145856) != 0)) {
        setState(112);
        complex(0);
      }
      setState(115);
      match(ExtendedDiracParser::SUM);
      setState(116);
      varcons(0);
      setState(117);
      match(ExtendedDiracParser::BAR);
      setState(118);
      antlrcpp::downCast<TermContext *>(_localctx)->VStr = match(ExtendedDiracParser::STR);
      setState(119);
      match(ExtendedDiracParser::RIGHT_ANGLE_BRACKET);
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(121);
      match(ExtendedDiracParser::SUB);
      setState(122);
      match(ExtendedDiracParser::BAR);
      setState(123);
      antlrcpp::downCast<TermContext *>(_localctx)->VStr = match(ExtendedDiracParser::STR);
      setState(124);
      match(ExtendedDiracParser::RIGHT_ANGLE_BRACKET);
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(125);
      match(ExtendedDiracParser::SUB);
      setState(126);
      match(ExtendedDiracParser::SUM);
      setState(127);
      varcons(0);
      setState(128);
      match(ExtendedDiracParser::BAR);
      setState(129);
      antlrcpp::downCast<TermContext *>(_localctx)->VStr = match(ExtendedDiracParser::STR);
      setState(130);
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
    setState(148);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 11, _ctx)) {
    case 1: {
      setState(135);
      antlrcpp::downCast<ComplexContext *>(_localctx)->sub = match(ExtendedDiracParser::SUB);
      setState(136);
      complex(6);
      break;
    }

    case 2: {
      setState(137);
      match(ExtendedDiracParser::LEFT_PARENTHESIS);
      setState(138);
      complex(0);
      setState(139);
      match(ExtendedDiracParser::RIGHT_PARENTHESIS);
      break;
    }

    case 3: {
      setState(141);
      antlrcpp::downCast<ComplexContext *>(_localctx)->func = match(ExtendedDiracParser::STR);
      setState(142);
      match(ExtendedDiracParser::LEFT_PARENTHESIS);
      setState(143);
      complex(0);
      setState(144);
      match(ExtendedDiracParser::RIGHT_PARENTHESIS);
      setState(145);

      if (!( (antlrcpp::downCast<ComplexContext *>(_localctx)->func != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->func->getText() : "") == "real" || (antlrcpp::downCast<ComplexContext *>(_localctx)->func != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->func->getText() : "") == "imag" || (antlrcpp::downCast<ComplexContext *>(_localctx)->func != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->func->getText() : "") == "eipi" || (antlrcpp::downCast<ComplexContext *>(_localctx)->func != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->func->getText() : "") == "ei2pi" )) throw FailedPredicateException(this, " $func.text == \"real\" || $func.text == \"imag\" || $func.text == \"eipi\" || $func.text == \"ei2pi\" ");
      break;
    }

    case 4: {
      setState(147);
      antlrcpp::downCast<ComplexContext *>(_localctx)->var = match(ExtendedDiracParser::STR);
      break;
    }

    default:
      break;
    }
    _ctx->stop = _input->LT(-1);
    setState(162);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 13, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        setState(160);
        _errHandler->sync(this);
        switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 12, _ctx)) {
        case 1: {
          _localctx = _tracker.createInstance<ComplexContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleComplex);
          setState(150);

          if (!(precpred(_ctx, 5))) throw FailedPredicateException(this, "precpred(_ctx, 5)");
          setState(151);
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
          setState(152);
          complex(6);
          break;
        }

        case 2: {
          _localctx = _tracker.createInstance<ComplexContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleComplex);
          setState(153);

          if (!(precpred(_ctx, 4))) throw FailedPredicateException(this, "precpred(_ctx, 4)");
          setState(154);
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
          setState(155);
          complex(5);
          break;
        }

        case 3: {
          _localctx = _tracker.createInstance<ComplexContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleComplex);
          setState(156);

          if (!(precpred(_ctx, 7))) throw FailedPredicateException(this, "precpred(_ctx, 7)");
          setState(157);
          match(ExtendedDiracParser::POWER);
          setState(158);
          antlrcpp::downCast<ComplexContext *>(_localctx)->n = match(ExtendedDiracParser::STR);
          setState(159);

          if (!( isNonZero((antlrcpp::downCast<ComplexContext *>(_localctx)->n != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->n->getText() : "")) )) throw FailedPredicateException(this, " isNonZero($n.text) ");
          break;
        }

        default:
          break;
        } 
      }
      setState(164);
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

//----------------- AngleContext ------------------------------------------------------------------

ExtendedDiracParser::AngleContext::AngleContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* ExtendedDiracParser::AngleContext::DIV() {
  return getToken(ExtendedDiracParser::DIV, 0);
}

std::vector<tree::TerminalNode *> ExtendedDiracParser::AngleContext::STR() {
  return getTokens(ExtendedDiracParser::STR);
}

tree::TerminalNode* ExtendedDiracParser::AngleContext::STR(size_t i) {
  return getToken(ExtendedDiracParser::STR, i);
}

tree::TerminalNode* ExtendedDiracParser::AngleContext::SUB() {
  return getToken(ExtendedDiracParser::SUB, 0);
}


size_t ExtendedDiracParser::AngleContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleAngle;
}

void ExtendedDiracParser::AngleContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterAngle(this);
}

void ExtendedDiracParser::AngleContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitAngle(this);
}


std::any ExtendedDiracParser::AngleContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitAngle(this);
  else
    return visitor->visitChildren(this);
}

ExtendedDiracParser::AngleContext* ExtendedDiracParser::angle() {
  AngleContext *_localctx = _tracker.createInstance<AngleContext>(_ctx, getState());
  enterRule(_localctx, 16, ExtendedDiracParser::RuleAngle);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(177);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 16, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(166);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == ExtendedDiracParser::SUB) {
        setState(165);
        match(ExtendedDiracParser::SUB);
      }
      setState(168);
      antlrcpp::downCast<AngleContext *>(_localctx)->x = match(ExtendedDiracParser::STR);
      setState(169);
      match(ExtendedDiracParser::DIV);
      setState(170);
      antlrcpp::downCast<AngleContext *>(_localctx)->y = match(ExtendedDiracParser::STR);
      setState(171);

      if (!( areAllDigits((antlrcpp::downCast<AngleContext *>(_localctx)->x != nullptr ? antlrcpp::downCast<AngleContext *>(_localctx)->x->getText() : "")) && isNonZero((antlrcpp::downCast<AngleContext *>(_localctx)->y != nullptr ? antlrcpp::downCast<AngleContext *>(_localctx)->y->getText() : "")) )) throw FailedPredicateException(this, " areAllDigits($x.text) && isNonZero($y.text) ");
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(173);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == ExtendedDiracParser::SUB) {
        setState(172);
        match(ExtendedDiracParser::SUB);
      }
      setState(175);
      antlrcpp::downCast<AngleContext *>(_localctx)->n = match(ExtendedDiracParser::STR);
      setState(176);

      if (!( areAllDigits((antlrcpp::downCast<AngleContext *>(_localctx)->n != nullptr ? antlrcpp::downCast<AngleContext *>(_localctx)->n->getText() : "")) )) throw FailedPredicateException(this, " areAllDigits($n.text) ");
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
  size_t startState = 18;
  enterRecursionRule(_localctx, 18, ExtendedDiracParser::RuleVarcons, precedence);

    

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
    setState(180);
    varcon();
    _ctx->stop = _input->LT(-1);
    setState(187);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 17, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<VarconsContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleVarcons);
        setState(182);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(183);
        match(ExtendedDiracParser::COMMA);
        setState(184);
        varcon(); 
      }
      setState(189);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 17, _ctx);
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
  enterRule(_localctx, 20, ExtendedDiracParser::RuleVarcon);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(198);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 18, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(190);
      match(ExtendedDiracParser::BAR);
      setState(191);
      antlrcpp::downCast<VarconContext *>(_localctx)->V = match(ExtendedDiracParser::STR);
      setState(192);
      match(ExtendedDiracParser::BAR);
      setState(193);
      match(ExtendedDiracParser::EQ);
      setState(194);
      antlrcpp::downCast<VarconContext *>(_localctx)->N = match(ExtendedDiracParser::STR);
      setState(195);

      if (!( isALowercaseLetter((antlrcpp::downCast<VarconContext *>(_localctx)->V != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->V->getText() : "")) && isNonZero((antlrcpp::downCast<VarconContext *>(_localctx)->N != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->N->getText() : "")) )) throw FailedPredicateException(this, " isALowercaseLetter($V.text) && isNonZero($N.text) ");
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(196);
      eq();
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(197);
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
  enterRule(_localctx, 22, ExtendedDiracParser::RuleEq);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(200);
    complex(0);
    setState(201);
    match(ExtendedDiracParser::EQ);
    setState(202);
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
  enterRule(_localctx, 24, ExtendedDiracParser::RuleIneq);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(204);
    complex(0);
    setState(205);
    match(ExtendedDiracParser::NE);
    setState(206);
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
  size_t startState = 26;
  enterRecursionRule(_localctx, 26, ExtendedDiracParser::RulePredicate, precedence);

    

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
    setState(233);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 19, _ctx)) {
    case 1: {
      setState(209);
      eq();
      break;
    }

    case 2: {
      setState(210);
      ineq();
      break;
    }

    case 3: {
      setState(211);
      complex(0);
      setState(212);
      match(ExtendedDiracParser::LESS_THAN);
      setState(213);
      complex(0);
      break;
    }

    case 4: {
      setState(215);
      complex(0);
      setState(216);
      match(ExtendedDiracParser::LESS_EQUAL);
      setState(217);
      complex(0);
      break;
    }

    case 5: {
      setState(219);
      complex(0);
      setState(220);
      match(ExtendedDiracParser::RIGHT_ANGLE_BRACKET);
      setState(221);
      complex(0);
      break;
    }

    case 6: {
      setState(223);
      complex(0);
      setState(224);
      match(ExtendedDiracParser::GREATER_EQUAL);
      setState(225);
      complex(0);
      break;
    }

    case 7: {
      setState(227);
      match(ExtendedDiracParser::LOGICAL_NOT);
      setState(228);
      predicate(4);
      break;
    }

    case 8: {
      setState(229);
      match(ExtendedDiracParser::LEFT_PARENTHESIS);
      setState(230);
      predicate(0);
      setState(231);
      match(ExtendedDiracParser::RIGHT_PARENTHESIS);
      break;
    }

    default:
      break;
    }
    _ctx->stop = _input->LT(-1);
    setState(243);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 21, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        setState(241);
        _errHandler->sync(this);
        switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 20, _ctx)) {
        case 1: {
          _localctx = _tracker.createInstance<PredicateContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RulePredicate);
          setState(235);

          if (!(precpred(_ctx, 3))) throw FailedPredicateException(this, "precpred(_ctx, 3)");
          setState(236);
          match(ExtendedDiracParser::LOGICAL_AND);
          setState(237);
          predicate(4);
          break;
        }

        case 2: {
          _localctx = _tracker.createInstance<PredicateContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RulePredicate);
          setState(238);

          if (!(precpred(_ctx, 2))) throw FailedPredicateException(this, "precpred(_ctx, 2)");
          setState(239);
          match(ExtendedDiracParser::LOGICAL_OR);
          setState(240);
          predicate(3);
          break;
        }

        default:
          break;
        } 
      }
      setState(245);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 21, _ctx);
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
    case 8: return angleSempred(antlrcpp::downCast<AngleContext *>(context), predicateIndex);
    case 9: return varconsSempred(antlrcpp::downCast<VarconsContext *>(context), predicateIndex);
    case 10: return varconSempred(antlrcpp::downCast<VarconContext *>(context), predicateIndex);
    case 13: return predicateSempred(antlrcpp::downCast<PredicateContext *>(context), predicateIndex);

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
    case 10: return  isNonZero((antlrcpp::downCast<ComplexContext *>(_localctx)->n != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->n->getText() : "")) ;

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::angleSempred(AngleContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 11: return  areAllDigits((antlrcpp::downCast<AngleContext *>(_localctx)->x != nullptr ? antlrcpp::downCast<AngleContext *>(_localctx)->x->getText() : "")) && isNonZero((antlrcpp::downCast<AngleContext *>(_localctx)->y != nullptr ? antlrcpp::downCast<AngleContext *>(_localctx)->y->getText() : "")) ;
    case 12: return  areAllDigits((antlrcpp::downCast<AngleContext *>(_localctx)->n != nullptr ? antlrcpp::downCast<AngleContext *>(_localctx)->n->getText() : "")) ;

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::varconsSempred(VarconsContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 13: return precpred(_ctx, 1);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::varconSempred(VarconContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 14: return  isALowercaseLetter((antlrcpp::downCast<VarconContext *>(_localctx)->V != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->V->getText() : "")) && isNonZero((antlrcpp::downCast<VarconContext *>(_localctx)->N != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->N->getText() : "")) ;

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::predicateSempred(PredicateContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 15: return precpred(_ctx, 3);
    case 16: return precpred(_ctx, 2);

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
