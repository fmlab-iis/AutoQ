
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
      "expr", "tset", "scset", "set", "diracs", "dirac", "term", "varcons", 
      "varcon", "ineq"
    },
    std::vector<std::string>{
      "", "'+'", "'|'", "','", "':'", "'='", "'{'", "'\\u2260'", "", "'\\u2228'", 
      "'^'", "'''", "'\\u2297'", "", "'}'", "';'", "'\\'", "", "", "'\\u222A'"
    },
    std::vector<std::string>{
      "", "ADD", "BAR", "COMMA", "COLON", "EQ", "LEFT_BRACE", "NE", "NEWLINES", 
      "OR", "POWER", "PRIME", "PROD", "RIGHT_ANGLE_BRACKET", "RIGHT_BRACE", 
      "SEMICOLON", "SETMINUS", "STR", "SUM", "UNION", "WS"
    }
  );
  static const int32_t serializedATNSegment[] = {
  	4,1,20,141,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,6,2,
  	7,7,7,2,8,7,8,2,9,7,9,1,0,1,0,1,0,1,0,1,0,3,0,26,8,0,1,1,1,1,1,1,1,1,
  	1,1,1,1,1,1,3,1,35,8,1,1,1,1,1,1,1,5,1,40,8,1,10,1,12,1,43,9,1,1,2,1,
  	2,1,2,1,2,1,2,1,2,5,2,51,8,2,10,2,12,2,54,9,2,1,3,1,3,1,3,1,3,1,3,1,3,
  	1,3,1,3,1,3,1,3,1,3,3,3,67,8,3,1,3,1,3,1,3,5,3,72,8,3,10,3,12,3,75,9,
  	3,1,4,1,4,1,4,1,4,1,4,1,4,5,4,83,8,4,10,4,12,4,86,9,4,1,5,1,5,1,5,1,5,
  	1,5,1,5,5,5,94,8,5,10,5,12,5,97,9,5,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,
  	6,1,6,1,6,3,6,110,8,6,1,7,1,7,1,7,1,7,1,7,1,7,5,7,118,8,7,10,7,12,7,121,
  	9,7,1,8,1,8,1,8,1,8,1,8,1,8,1,8,1,8,1,8,1,8,1,8,3,8,134,8,8,1,9,1,9,1,
  	9,1,9,1,9,1,9,0,6,2,4,6,8,10,14,10,0,2,4,6,8,10,12,14,16,18,0,0,142,0,
  	25,1,0,0,0,2,34,1,0,0,0,4,44,1,0,0,0,6,66,1,0,0,0,8,76,1,0,0,0,10,87,
  	1,0,0,0,12,109,1,0,0,0,14,111,1,0,0,0,16,133,1,0,0,0,18,135,1,0,0,0,20,
  	26,3,2,1,0,21,22,3,2,1,0,22,23,5,16,0,0,23,24,3,2,1,0,24,26,1,0,0,0,25,
  	20,1,0,0,0,25,21,1,0,0,0,26,1,1,0,0,0,27,28,6,1,-1,0,28,35,3,4,2,0,29,
  	30,3,6,3,0,30,31,5,10,0,0,31,32,5,17,0,0,32,33,4,1,0,1,33,35,1,0,0,0,
  	34,27,1,0,0,0,34,29,1,0,0,0,35,41,1,0,0,0,36,37,10,1,0,0,37,38,5,12,0,
  	0,38,40,3,2,1,2,39,36,1,0,0,0,40,43,1,0,0,0,41,39,1,0,0,0,41,42,1,0,0,
  	0,42,3,1,0,0,0,43,41,1,0,0,0,44,45,6,2,-1,0,45,46,3,6,3,0,46,52,1,0,0,
  	0,47,48,10,2,0,0,48,49,5,15,0,0,49,51,3,6,3,0,50,47,1,0,0,0,51,54,1,0,
  	0,0,52,50,1,0,0,0,52,53,1,0,0,0,53,5,1,0,0,0,54,52,1,0,0,0,55,56,6,3,
  	-1,0,56,57,5,6,0,0,57,58,3,8,4,0,58,59,5,14,0,0,59,67,1,0,0,0,60,61,5,
  	6,0,0,61,62,3,8,4,0,62,63,5,4,0,0,63,64,3,14,7,0,64,65,5,14,0,0,65,67,
  	1,0,0,0,66,55,1,0,0,0,66,60,1,0,0,0,67,73,1,0,0,0,68,69,10,3,0,0,69,70,
  	5,19,0,0,70,72,3,6,3,4,71,68,1,0,0,0,72,75,1,0,0,0,73,71,1,0,0,0,73,74,
  	1,0,0,0,74,7,1,0,0,0,75,73,1,0,0,0,76,77,6,4,-1,0,77,78,3,10,5,0,78,84,
  	1,0,0,0,79,80,10,1,0,0,80,81,5,3,0,0,81,83,3,10,5,0,82,79,1,0,0,0,83,
  	86,1,0,0,0,84,82,1,0,0,0,84,85,1,0,0,0,85,9,1,0,0,0,86,84,1,0,0,0,87,
  	88,6,5,-1,0,88,89,3,12,6,0,89,95,1,0,0,0,90,91,10,1,0,0,91,92,5,1,0,0,
  	92,94,3,12,6,0,93,90,1,0,0,0,94,97,1,0,0,0,95,93,1,0,0,0,95,96,1,0,0,
  	0,96,11,1,0,0,0,97,95,1,0,0,0,98,99,5,17,0,0,99,100,5,2,0,0,100,101,5,
  	17,0,0,101,110,5,13,0,0,102,103,5,17,0,0,103,104,5,18,0,0,104,105,3,14,
  	7,0,105,106,5,2,0,0,106,107,5,17,0,0,107,108,5,13,0,0,108,110,1,0,0,0,
  	109,98,1,0,0,0,109,102,1,0,0,0,110,13,1,0,0,0,111,112,6,7,-1,0,112,113,
  	3,16,8,0,113,119,1,0,0,0,114,115,10,1,0,0,115,116,5,3,0,0,116,118,3,16,
  	8,0,117,114,1,0,0,0,118,121,1,0,0,0,119,117,1,0,0,0,119,120,1,0,0,0,120,
  	15,1,0,0,0,121,119,1,0,0,0,122,123,5,2,0,0,123,124,5,17,0,0,124,125,5,
  	2,0,0,125,126,5,5,0,0,126,127,5,17,0,0,127,134,4,8,7,1,128,129,5,17,0,
  	0,129,130,5,5,0,0,130,131,5,17,0,0,131,134,4,8,8,1,132,134,3,18,9,0,133,
  	122,1,0,0,0,133,128,1,0,0,0,133,132,1,0,0,0,134,17,1,0,0,0,135,136,5,
  	17,0,0,136,137,5,7,0,0,137,138,5,17,0,0,138,139,4,9,9,1,139,19,1,0,0,
  	0,11,25,34,41,52,66,73,84,95,109,119,133
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
    setState(25);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 0, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(20);
      tset(0);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(21);
      tset(0);
      setState(22);
      antlrcpp::downCast<ExprContext *>(_localctx)->op = match(ExtendedDiracParser::SETMINUS);
      setState(23);
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
    setState(34);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 1, _ctx)) {
    case 1: {
      setState(28);
      scset(0);
      break;
    }

    case 2: {
      setState(29);
      set(0);
      setState(30);
      antlrcpp::downCast<TsetContext *>(_localctx)->op = match(ExtendedDiracParser::POWER);
      setState(31);
      antlrcpp::downCast<TsetContext *>(_localctx)->N = match(ExtendedDiracParser::STR);
      setState(32);

      if (!(isNonZero((antlrcpp::downCast<TsetContext *>(_localctx)->N != nullptr ? antlrcpp::downCast<TsetContext *>(_localctx)->N->getText() : "")))) throw FailedPredicateException(this, "isNonZero($N.text)");
      break;
    }

    default:
      break;
    }
    _ctx->stop = _input->LT(-1);
    setState(41);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 2, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<TsetContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleTset);
        setState(36);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(37);
        antlrcpp::downCast<TsetContext *>(_localctx)->op = match(ExtendedDiracParser::PROD);
        setState(38);
        tset(2); 
      }
      setState(43);
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
    setState(45);
    set(0);
    _ctx->stop = _input->LT(-1);
    setState(52);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 3, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<ScsetContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleScset);
        setState(47);

        if (!(precpred(_ctx, 2))) throw FailedPredicateException(this, "precpred(_ctx, 2)");
        setState(48);
        antlrcpp::downCast<ScsetContext *>(_localctx)->op = match(ExtendedDiracParser::SEMICOLON);
        setState(49);
        set(0); 
      }
      setState(54);
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
    setState(66);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 4, _ctx)) {
    case 1: {
      setState(56);
      match(ExtendedDiracParser::LEFT_BRACE);
      setState(57);
      diracs(0);
      setState(58);
      match(ExtendedDiracParser::RIGHT_BRACE);
      break;
    }

    case 2: {
      setState(60);
      match(ExtendedDiracParser::LEFT_BRACE);
      setState(61);
      diracs(0);
      setState(62);
      match(ExtendedDiracParser::COLON);
      setState(63);
      varcons(0);
      setState(64);
      match(ExtendedDiracParser::RIGHT_BRACE);
      break;
    }

    default:
      break;
    }
    _ctx->stop = _input->LT(-1);
    setState(73);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 5, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<SetContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleSet);
        setState(68);

        if (!(precpred(_ctx, 3))) throw FailedPredicateException(this, "precpred(_ctx, 3)");
        setState(69);
        antlrcpp::downCast<SetContext *>(_localctx)->op = match(ExtendedDiracParser::UNION);
        setState(70);
        set(4); 
      }
      setState(75);
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
    setState(77);
    dirac(0);
    _ctx->stop = _input->LT(-1);
    setState(84);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 6, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<DiracsContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleDiracs);
        setState(79);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(80);
        match(ExtendedDiracParser::COMMA);
        setState(81);
        dirac(0); 
      }
      setState(86);
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
    setState(88);
    term();
    _ctx->stop = _input->LT(-1);
    setState(95);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 7, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<DiracContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleDirac);
        setState(90);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(91);
        antlrcpp::downCast<DiracContext *>(_localctx)->op = match(ExtendedDiracParser::ADD);
        setState(92);
        term(); 
      }
      setState(97);
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

std::vector<tree::TerminalNode *> ExtendedDiracParser::TermContext::STR() {
  return getTokens(ExtendedDiracParser::STR);
}

tree::TerminalNode* ExtendedDiracParser::TermContext::STR(size_t i) {
  return getToken(ExtendedDiracParser::STR, i);
}

tree::TerminalNode* ExtendedDiracParser::TermContext::SUM() {
  return getToken(ExtendedDiracParser::SUM, 0);
}

ExtendedDiracParser::VarconsContext* ExtendedDiracParser::TermContext::varcons() {
  return getRuleContext<ExtendedDiracParser::VarconsContext>(0);
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

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(109);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 8, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(98);
      antlrcpp::downCast<TermContext *>(_localctx)->C = match(ExtendedDiracParser::STR);
      setState(99);
      match(ExtendedDiracParser::BAR);
      setState(100);
      antlrcpp::downCast<TermContext *>(_localctx)->VStr = match(ExtendedDiracParser::STR);
      setState(101);
      match(ExtendedDiracParser::RIGHT_ANGLE_BRACKET);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(102);
      antlrcpp::downCast<TermContext *>(_localctx)->C = match(ExtendedDiracParser::STR);
      setState(103);
      match(ExtendedDiracParser::SUM);
      setState(104);
      varcons(0);
      setState(105);
      match(ExtendedDiracParser::BAR);
      setState(106);
      antlrcpp::downCast<TermContext *>(_localctx)->VStr = match(ExtendedDiracParser::STR);
      setState(107);
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
  size_t startState = 14;
  enterRecursionRule(_localctx, 14, ExtendedDiracParser::RuleVarcons, precedence);

    

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
    setState(112);
    varcon();
    _ctx->stop = _input->LT(-1);
    setState(119);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 9, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<VarconsContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleVarcons);
        setState(114);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(115);
        match(ExtendedDiracParser::COMMA);
        setState(116);
        varcon(); 
      }
      setState(121);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 9, _ctx);
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
  enterRule(_localctx, 16, ExtendedDiracParser::RuleVarcon);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(133);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 10, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(122);
      match(ExtendedDiracParser::BAR);
      setState(123);
      antlrcpp::downCast<VarconContext *>(_localctx)->V = match(ExtendedDiracParser::STR);
      setState(124);
      match(ExtendedDiracParser::BAR);
      setState(125);
      match(ExtendedDiracParser::EQ);
      setState(126);
      antlrcpp::downCast<VarconContext *>(_localctx)->N = match(ExtendedDiracParser::STR);
      setState(127);

      if (!(isALowercaseLetter((antlrcpp::downCast<VarconContext *>(_localctx)->V != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->V->getText() : "")) && isNonZero((antlrcpp::downCast<VarconContext *>(_localctx)->N != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->N->getText() : "")))) throw FailedPredicateException(this, "isALowercaseLetter($V.text) && isNonZero($N.text)");
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(128);
      antlrcpp::downCast<VarconContext *>(_localctx)->V = match(ExtendedDiracParser::STR);
      setState(129);
      match(ExtendedDiracParser::EQ);
      setState(130);
      antlrcpp::downCast<VarconContext *>(_localctx)->CStr = match(ExtendedDiracParser::STR);
      setState(131);

      if (!(isALowercaseLetter((antlrcpp::downCast<VarconContext *>(_localctx)->V != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->V->getText() : "")) && isAConstantBinaryString((antlrcpp::downCast<VarconContext *>(_localctx)->CStr != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->CStr->getText() : "")))) throw FailedPredicateException(this, "isALowercaseLetter($V.text) && isAConstantBinaryString($CStr.text)");
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(132);
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

//----------------- IneqContext ------------------------------------------------------------------

ExtendedDiracParser::IneqContext::IneqContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* ExtendedDiracParser::IneqContext::NE() {
  return getToken(ExtendedDiracParser::NE, 0);
}

std::vector<tree::TerminalNode *> ExtendedDiracParser::IneqContext::STR() {
  return getTokens(ExtendedDiracParser::STR);
}

tree::TerminalNode* ExtendedDiracParser::IneqContext::STR(size_t i) {
  return getToken(ExtendedDiracParser::STR, i);
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
  enterRule(_localctx, 18, ExtendedDiracParser::RuleIneq);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(135);
    antlrcpp::downCast<IneqContext *>(_localctx)->L = match(ExtendedDiracParser::STR);
    setState(136);
    match(ExtendedDiracParser::NE);
    setState(137);
    antlrcpp::downCast<IneqContext *>(_localctx)->R = match(ExtendedDiracParser::STR);
    setState(138);

    if (!(isALowercaseLetter((antlrcpp::downCast<IneqContext *>(_localctx)->L != nullptr ? antlrcpp::downCast<IneqContext *>(_localctx)->L->getText() : "")) && (isALowercaseLetter((antlrcpp::downCast<IneqContext *>(_localctx)->R != nullptr ? antlrcpp::downCast<IneqContext *>(_localctx)->R->getText() : "")) || isAConstantBinaryString((antlrcpp::downCast<IneqContext *>(_localctx)->R != nullptr ? antlrcpp::downCast<IneqContext *>(_localctx)->R->getText() : ""))))) throw FailedPredicateException(this, "isALowercaseLetter($L.text) && (isALowercaseLetter($R.text) || isAConstantBinaryString($R.text))");
   
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
    case 7: return varconsSempred(antlrcpp::downCast<VarconsContext *>(context), predicateIndex);
    case 8: return varconSempred(antlrcpp::downCast<VarconContext *>(context), predicateIndex);
    case 9: return ineqSempred(antlrcpp::downCast<IneqContext *>(context), predicateIndex);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::tsetSempred(TsetContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 0: return isNonZero((antlrcpp::downCast<TsetContext *>(_localctx)->N != nullptr ? antlrcpp::downCast<TsetContext *>(_localctx)->N->getText() : ""));
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

bool ExtendedDiracParser::varconsSempred(VarconsContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 6: return precpred(_ctx, 1);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::varconSempred(VarconContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 7: return isALowercaseLetter((antlrcpp::downCast<VarconContext *>(_localctx)->V != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->V->getText() : "")) && isNonZero((antlrcpp::downCast<VarconContext *>(_localctx)->N != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->N->getText() : ""));
    case 8: return isALowercaseLetter((antlrcpp::downCast<VarconContext *>(_localctx)->V != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->V->getText() : "")) && isAConstantBinaryString((antlrcpp::downCast<VarconContext *>(_localctx)->CStr != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->CStr->getText() : ""));

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::ineqSempred(IneqContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 9: return isALowercaseLetter((antlrcpp::downCast<IneqContext *>(_localctx)->L != nullptr ? antlrcpp::downCast<IneqContext *>(_localctx)->L->getText() : "")) && (isALowercaseLetter((antlrcpp::downCast<IneqContext *>(_localctx)->R != nullptr ? antlrcpp::downCast<IneqContext *>(_localctx)->R->getText() : "")) || isAConstantBinaryString((antlrcpp::downCast<IneqContext *>(_localctx)->R != nullptr ? antlrcpp::downCast<IneqContext *>(_localctx)->R->getText() : "")));

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
