
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
      "expr", "tset", "set", "diracs", "dirac", "term", "varcons", "varcon", 
      "ineq"
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
  	4,1,19,127,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,6,2,
  	7,7,7,2,8,7,8,1,0,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,3,1,
  	32,8,1,1,1,1,1,1,1,5,1,37,8,1,10,1,12,1,40,9,1,1,2,1,2,1,2,1,2,1,2,1,
  	2,1,2,1,2,1,2,1,2,1,2,3,2,53,8,2,1,2,1,2,1,2,5,2,58,8,2,10,2,12,2,61,
  	9,2,1,3,1,3,1,3,1,3,1,3,1,3,5,3,69,8,3,10,3,12,3,72,9,3,1,4,1,4,1,4,1,
  	4,1,4,1,4,5,4,80,8,4,10,4,12,4,83,9,4,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,
  	1,5,1,5,1,5,3,5,96,8,5,1,6,1,6,1,6,1,6,1,6,1,6,5,6,104,8,6,10,6,12,6,
  	107,9,6,1,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,3,7,120,8,7,1,8,1,
  	8,1,8,1,8,1,8,1,8,0,5,2,4,6,8,12,9,0,2,4,6,8,10,12,14,16,0,0,128,0,18,
  	1,0,0,0,2,31,1,0,0,0,4,52,1,0,0,0,6,62,1,0,0,0,8,73,1,0,0,0,10,95,1,0,
  	0,0,12,97,1,0,0,0,14,119,1,0,0,0,16,121,1,0,0,0,18,19,3,2,1,0,19,1,1,
  	0,0,0,20,21,6,1,-1,0,21,32,3,4,2,0,22,23,3,4,2,0,23,24,5,10,0,0,24,25,
  	5,16,0,0,25,26,4,1,0,1,26,32,1,0,0,0,27,28,3,4,2,0,28,29,5,15,0,0,29,
  	30,3,4,2,0,30,32,1,0,0,0,31,20,1,0,0,0,31,22,1,0,0,0,31,27,1,0,0,0,32,
  	38,1,0,0,0,33,34,10,2,0,0,34,35,5,12,0,0,35,37,3,2,1,3,36,33,1,0,0,0,
  	37,40,1,0,0,0,38,36,1,0,0,0,38,39,1,0,0,0,39,3,1,0,0,0,40,38,1,0,0,0,
  	41,42,6,2,-1,0,42,43,5,6,0,0,43,44,3,6,3,0,44,45,5,14,0,0,45,53,1,0,0,
  	0,46,47,5,6,0,0,47,48,3,6,3,0,48,49,5,4,0,0,49,50,3,12,6,0,50,51,5,14,
  	0,0,51,53,1,0,0,0,52,41,1,0,0,0,52,46,1,0,0,0,53,59,1,0,0,0,54,55,10,
  	3,0,0,55,56,5,18,0,0,56,58,3,4,2,4,57,54,1,0,0,0,58,61,1,0,0,0,59,57,
  	1,0,0,0,59,60,1,0,0,0,60,5,1,0,0,0,61,59,1,0,0,0,62,63,6,3,-1,0,63,64,
  	3,8,4,0,64,70,1,0,0,0,65,66,10,1,0,0,66,67,5,3,0,0,67,69,3,8,4,0,68,65,
  	1,0,0,0,69,72,1,0,0,0,70,68,1,0,0,0,70,71,1,0,0,0,71,7,1,0,0,0,72,70,
  	1,0,0,0,73,74,6,4,-1,0,74,75,3,10,5,0,75,81,1,0,0,0,76,77,10,1,0,0,77,
  	78,5,1,0,0,78,80,3,10,5,0,79,76,1,0,0,0,80,83,1,0,0,0,81,79,1,0,0,0,81,
  	82,1,0,0,0,82,9,1,0,0,0,83,81,1,0,0,0,84,85,5,16,0,0,85,86,5,2,0,0,86,
  	87,5,16,0,0,87,96,5,13,0,0,88,89,5,16,0,0,89,90,5,17,0,0,90,91,3,12,6,
  	0,91,92,5,2,0,0,92,93,5,16,0,0,93,94,5,13,0,0,94,96,1,0,0,0,95,84,1,0,
  	0,0,95,88,1,0,0,0,96,11,1,0,0,0,97,98,6,6,-1,0,98,99,3,14,7,0,99,105,
  	1,0,0,0,100,101,10,1,0,0,101,102,5,3,0,0,102,104,3,14,7,0,103,100,1,0,
  	0,0,104,107,1,0,0,0,105,103,1,0,0,0,105,106,1,0,0,0,106,13,1,0,0,0,107,
  	105,1,0,0,0,108,109,5,2,0,0,109,110,5,16,0,0,110,111,5,2,0,0,111,112,
  	5,5,0,0,112,113,5,16,0,0,113,120,4,7,6,1,114,115,5,16,0,0,115,116,5,5,
  	0,0,116,117,5,16,0,0,117,120,4,7,7,1,118,120,3,16,8,0,119,108,1,0,0,0,
  	119,114,1,0,0,0,119,118,1,0,0,0,120,15,1,0,0,0,121,122,5,16,0,0,122,123,
  	5,7,0,0,123,124,5,16,0,0,124,125,4,8,8,1,125,17,1,0,0,0,9,31,38,52,59,
  	70,81,95,105,119
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

ExtendedDiracParser::TsetContext* ExtendedDiracParser::ExprContext::tset() {
  return getRuleContext<ExtendedDiracParser::TsetContext>(0);
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
    enterOuterAlt(_localctx, 1);
    setState(18);
    tset(0);
   
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

std::vector<ExtendedDiracParser::SetContext *> ExtendedDiracParser::TsetContext::set() {
  return getRuleContexts<ExtendedDiracParser::SetContext>();
}

ExtendedDiracParser::SetContext* ExtendedDiracParser::TsetContext::set(size_t i) {
  return getRuleContext<ExtendedDiracParser::SetContext>(i);
}

tree::TerminalNode* ExtendedDiracParser::TsetContext::POWER() {
  return getToken(ExtendedDiracParser::POWER, 0);
}

tree::TerminalNode* ExtendedDiracParser::TsetContext::STR() {
  return getToken(ExtendedDiracParser::STR, 0);
}

tree::TerminalNode* ExtendedDiracParser::TsetContext::SEMICOLON() {
  return getToken(ExtendedDiracParser::SEMICOLON, 0);
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
    setState(31);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 0, _ctx)) {
    case 1: {
      setState(21);
      set(0);
      break;
    }

    case 2: {
      setState(22);
      set(0);
      setState(23);
      antlrcpp::downCast<TsetContext *>(_localctx)->op = match(ExtendedDiracParser::POWER);
      setState(24);
      antlrcpp::downCast<TsetContext *>(_localctx)->N = match(ExtendedDiracParser::STR);
      setState(25);

      if (!(isNonZero((antlrcpp::downCast<TsetContext *>(_localctx)->N != nullptr ? antlrcpp::downCast<TsetContext *>(_localctx)->N->getText() : "")))) throw FailedPredicateException(this, "isNonZero($N.text)");
      break;
    }

    case 3: {
      setState(27);
      set(0);
      setState(28);
      antlrcpp::downCast<TsetContext *>(_localctx)->op = match(ExtendedDiracParser::SEMICOLON);
      setState(29);
      set(0);
      break;
    }

    default:
      break;
    }
    _ctx->stop = _input->LT(-1);
    setState(38);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 1, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<TsetContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleTset);
        setState(33);

        if (!(precpred(_ctx, 2))) throw FailedPredicateException(this, "precpred(_ctx, 2)");
        setState(34);
        antlrcpp::downCast<TsetContext *>(_localctx)->op = match(ExtendedDiracParser::PROD);
        setState(35);
        tset(3); 
      }
      setState(40);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 1, _ctx);
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
  size_t startState = 4;
  enterRecursionRule(_localctx, 4, ExtendedDiracParser::RuleSet, precedence);

    

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
    setState(52);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 2, _ctx)) {
    case 1: {
      setState(42);
      match(ExtendedDiracParser::LEFT_BRACE);
      setState(43);
      diracs(0);
      setState(44);
      match(ExtendedDiracParser::RIGHT_BRACE);
      break;
    }

    case 2: {
      setState(46);
      match(ExtendedDiracParser::LEFT_BRACE);
      setState(47);
      diracs(0);
      setState(48);
      match(ExtendedDiracParser::COLON);
      setState(49);
      varcons(0);
      setState(50);
      match(ExtendedDiracParser::RIGHT_BRACE);
      break;
    }

    default:
      break;
    }
    _ctx->stop = _input->LT(-1);
    setState(59);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 3, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<SetContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleSet);
        setState(54);

        if (!(precpred(_ctx, 3))) throw FailedPredicateException(this, "precpred(_ctx, 3)");
        setState(55);
        antlrcpp::downCast<SetContext *>(_localctx)->op = match(ExtendedDiracParser::UNION);
        setState(56);
        set(4); 
      }
      setState(61);
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
  size_t startState = 6;
  enterRecursionRule(_localctx, 6, ExtendedDiracParser::RuleDiracs, precedence);

    

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
    setState(63);
    dirac(0);
    _ctx->stop = _input->LT(-1);
    setState(70);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 4, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<DiracsContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleDiracs);
        setState(65);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(66);
        match(ExtendedDiracParser::COMMA);
        setState(67);
        dirac(0); 
      }
      setState(72);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 4, _ctx);
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
  size_t startState = 8;
  enterRecursionRule(_localctx, 8, ExtendedDiracParser::RuleDirac, precedence);

    

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
    term();
    _ctx->stop = _input->LT(-1);
    setState(81);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 5, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<DiracContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleDirac);
        setState(76);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(77);
        antlrcpp::downCast<DiracContext *>(_localctx)->op = match(ExtendedDiracParser::ADD);
        setState(78);
        term(); 
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
  enterRule(_localctx, 10, ExtendedDiracParser::RuleTerm);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(95);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 6, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(84);
      antlrcpp::downCast<TermContext *>(_localctx)->C = match(ExtendedDiracParser::STR);
      setState(85);
      match(ExtendedDiracParser::BAR);
      setState(86);
      antlrcpp::downCast<TermContext *>(_localctx)->VStr = match(ExtendedDiracParser::STR);
      setState(87);
      match(ExtendedDiracParser::RIGHT_ANGLE_BRACKET);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(88);
      antlrcpp::downCast<TermContext *>(_localctx)->C = match(ExtendedDiracParser::STR);
      setState(89);
      match(ExtendedDiracParser::SUM);
      setState(90);
      varcons(0);
      setState(91);
      match(ExtendedDiracParser::BAR);
      setState(92);
      antlrcpp::downCast<TermContext *>(_localctx)->VStr = match(ExtendedDiracParser::STR);
      setState(93);
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
  size_t startState = 12;
  enterRecursionRule(_localctx, 12, ExtendedDiracParser::RuleVarcons, precedence);

    

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
    setState(98);
    varcon();
    _ctx->stop = _input->LT(-1);
    setState(105);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 7, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<VarconsContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleVarcons);
        setState(100);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(101);
        match(ExtendedDiracParser::COMMA);
        setState(102);
        varcon(); 
      }
      setState(107);
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
  enterRule(_localctx, 14, ExtendedDiracParser::RuleVarcon);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(119);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 8, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(108);
      match(ExtendedDiracParser::BAR);
      setState(109);
      antlrcpp::downCast<VarconContext *>(_localctx)->V = match(ExtendedDiracParser::STR);
      setState(110);
      match(ExtendedDiracParser::BAR);
      setState(111);
      match(ExtendedDiracParser::EQ);
      setState(112);
      antlrcpp::downCast<VarconContext *>(_localctx)->N = match(ExtendedDiracParser::STR);
      setState(113);

      if (!(isALowercaseLetter((antlrcpp::downCast<VarconContext *>(_localctx)->V != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->V->getText() : "")) && isNonZero((antlrcpp::downCast<VarconContext *>(_localctx)->N != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->N->getText() : "")))) throw FailedPredicateException(this, "isALowercaseLetter($V.text) && isNonZero($N.text)");
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(114);
      antlrcpp::downCast<VarconContext *>(_localctx)->V = match(ExtendedDiracParser::STR);
      setState(115);
      match(ExtendedDiracParser::EQ);
      setState(116);
      antlrcpp::downCast<VarconContext *>(_localctx)->CStr = match(ExtendedDiracParser::STR);
      setState(117);

      if (!(isALowercaseLetter((antlrcpp::downCast<VarconContext *>(_localctx)->V != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->V->getText() : "")) && isAConstantBinaryString((antlrcpp::downCast<VarconContext *>(_localctx)->CStr != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->CStr->getText() : "")))) throw FailedPredicateException(this, "isALowercaseLetter($V.text) && isAConstantBinaryString($CStr.text)");
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(118);
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
  enterRule(_localctx, 16, ExtendedDiracParser::RuleIneq);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(121);
    antlrcpp::downCast<IneqContext *>(_localctx)->L = match(ExtendedDiracParser::STR);
    setState(122);
    match(ExtendedDiracParser::NE);
    setState(123);
    antlrcpp::downCast<IneqContext *>(_localctx)->R = match(ExtendedDiracParser::STR);
    setState(124);

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
    case 2: return setSempred(antlrcpp::downCast<SetContext *>(context), predicateIndex);
    case 3: return diracsSempred(antlrcpp::downCast<DiracsContext *>(context), predicateIndex);
    case 4: return diracSempred(antlrcpp::downCast<DiracContext *>(context), predicateIndex);
    case 6: return varconsSempred(antlrcpp::downCast<VarconsContext *>(context), predicateIndex);
    case 7: return varconSempred(antlrcpp::downCast<VarconContext *>(context), predicateIndex);
    case 8: return ineqSempred(antlrcpp::downCast<IneqContext *>(context), predicateIndex);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::tsetSempred(TsetContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 0: return isNonZero((antlrcpp::downCast<TsetContext *>(_localctx)->N != nullptr ? antlrcpp::downCast<TsetContext *>(_localctx)->N->getText() : ""));
    case 1: return precpred(_ctx, 2);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::setSempred(SetContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 2: return precpred(_ctx, 3);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::diracsSempred(DiracsContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 3: return precpred(_ctx, 1);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::diracSempred(DiracContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 4: return precpred(_ctx, 1);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::varconsSempred(VarconsContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 5: return precpred(_ctx, 1);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::varconSempred(VarconContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 6: return isALowercaseLetter((antlrcpp::downCast<VarconContext *>(_localctx)->V != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->V->getText() : "")) && isNonZero((antlrcpp::downCast<VarconContext *>(_localctx)->N != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->N->getText() : ""));
    case 7: return isALowercaseLetter((antlrcpp::downCast<VarconContext *>(_localctx)->V != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->V->getText() : "")) && isAConstantBinaryString((antlrcpp::downCast<VarconContext *>(_localctx)->CStr != nullptr ? antlrcpp::downCast<VarconContext *>(_localctx)->CStr->getText() : ""));

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::ineqSempred(IneqContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 8: return isALowercaseLetter((antlrcpp::downCast<IneqContext *>(_localctx)->L != nullptr ? antlrcpp::downCast<IneqContext *>(_localctx)->L->getText() : "")) && (isALowercaseLetter((antlrcpp::downCast<IneqContext *>(_localctx)->R != nullptr ? antlrcpp::downCast<IneqContext *>(_localctx)->R->getText() : "")) || isAConstantBinaryString((antlrcpp::downCast<IneqContext *>(_localctx)->R != nullptr ? antlrcpp::downCast<IneqContext *>(_localctx)->R->getText() : "")));

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
