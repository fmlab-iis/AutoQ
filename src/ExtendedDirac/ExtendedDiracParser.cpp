
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
      "extendedDirac", "set", "diracs", "dirac", "cket", "complex", "angle", 
      "ijklens", "ijklen"
    },
    std::vector<std::string>{
      "", "'+'", "'|'", "','", "'/'", "", "'ei2pi'", "'eipi'", "'='", "'\\u2229'", 
      "", "'('", "'{'", "'*'", "'^'", "'\\u2297'", "')'", "'}'", "'-'", 
      "'\\'", "'sqrt2'", "'\\u222A'"
    },
    std::vector<std::string>{
      "", "ADD", "BAR", "COMMA", "DIV", "DIGITS", "EI2PI", "EIPI", "EQ", 
      "INTERSECTION", "KET", "LEFT_BRACKET", "LEFT_CURLY_BRACKET", "MUL", 
      "POWER", "PROD", "RIGHT_BRACKET", "RIGHT_CURLY_BRACKET", "SUB", "SETMINUS", 
      "SQRT2", "UNION", "WS", "NAME"
    }
  );
  static const int32_t serializedATNSegment[] = {
  	4,1,23,161,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,6,2,
  	7,7,7,2,8,7,8,1,0,1,0,1,0,1,0,1,0,3,0,24,8,0,1,1,1,1,1,1,1,1,1,1,1,1,
  	1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,3,1,41,8,1,1,1,1,1,1,1,1,1,1,1,1,
  	1,1,1,1,1,1,1,1,1,5,1,53,8,1,10,1,12,1,56,9,1,1,2,1,2,1,2,1,2,1,2,1,2,
  	5,2,64,8,2,10,2,12,2,67,9,2,1,3,1,3,1,3,1,3,1,3,1,3,5,3,75,8,3,10,3,12,
  	3,78,9,3,1,4,1,4,1,4,1,4,1,4,3,4,85,8,4,1,4,1,4,1,4,1,5,1,5,1,5,1,5,1,
  	5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,3,5,
  	111,8,5,1,5,1,5,3,5,115,8,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,5,5,125,8,
  	5,10,5,12,5,128,9,5,1,6,3,6,131,8,6,1,6,1,6,1,6,1,6,1,6,3,6,138,8,6,1,
  	6,3,6,141,8,6,1,7,1,7,1,7,1,7,1,7,1,7,5,7,149,8,7,10,7,12,7,152,9,7,1,
  	8,1,8,1,8,1,8,1,8,1,8,1,8,1,8,0,5,2,4,6,10,14,9,0,2,4,6,8,10,12,14,16,
  	0,3,2,0,9,9,21,21,2,0,1,1,18,18,2,0,4,4,13,13,176,0,23,1,0,0,0,2,40,1,
  	0,0,0,4,57,1,0,0,0,6,68,1,0,0,0,8,84,1,0,0,0,10,110,1,0,0,0,12,140,1,
  	0,0,0,14,142,1,0,0,0,16,153,1,0,0,0,18,24,3,2,1,0,19,20,3,2,1,0,20,21,
  	5,19,0,0,21,22,3,2,1,0,22,24,1,0,0,0,23,18,1,0,0,0,23,19,1,0,0,0,24,1,
  	1,0,0,0,25,26,6,1,-1,0,26,27,5,11,0,0,27,28,3,2,1,0,28,29,5,16,0,0,29,
  	41,1,0,0,0,30,31,5,12,0,0,31,32,3,4,2,0,32,33,5,17,0,0,33,41,1,0,0,0,
  	34,35,5,12,0,0,35,36,3,6,3,0,36,37,5,2,0,0,37,38,3,14,7,0,38,39,5,17,
  	0,0,39,41,1,0,0,0,40,25,1,0,0,0,40,30,1,0,0,0,40,34,1,0,0,0,41,54,1,0,
  	0,0,42,43,10,2,0,0,43,44,5,15,0,0,44,53,3,2,1,3,45,46,10,1,0,0,46,47,
  	7,0,0,0,47,53,3,2,1,2,48,49,10,6,0,0,49,50,5,14,0,0,50,51,5,5,0,0,51,
  	53,4,1,3,1,52,42,1,0,0,0,52,45,1,0,0,0,52,48,1,0,0,0,53,56,1,0,0,0,54,
  	52,1,0,0,0,54,55,1,0,0,0,55,3,1,0,0,0,56,54,1,0,0,0,57,58,6,2,-1,0,58,
  	59,3,6,3,0,59,65,1,0,0,0,60,61,10,1,0,0,61,62,5,3,0,0,62,64,3,6,3,0,63,
  	60,1,0,0,0,64,67,1,0,0,0,65,63,1,0,0,0,65,66,1,0,0,0,66,5,1,0,0,0,67,
  	65,1,0,0,0,68,69,6,3,-1,0,69,70,3,8,4,0,70,76,1,0,0,0,71,72,10,1,0,0,
  	72,73,7,1,0,0,73,75,3,8,4,0,74,71,1,0,0,0,75,78,1,0,0,0,76,74,1,0,0,0,
  	76,77,1,0,0,0,77,7,1,0,0,0,78,76,1,0,0,0,79,85,3,10,5,0,80,81,3,10,5,
  	0,81,82,5,13,0,0,82,85,1,0,0,0,83,85,5,18,0,0,84,79,1,0,0,0,84,80,1,0,
  	0,0,84,83,1,0,0,0,84,85,1,0,0,0,85,86,1,0,0,0,86,87,5,10,0,0,87,88,6,
  	4,-1,0,88,9,1,0,0,0,89,90,6,5,-1,0,90,91,5,11,0,0,91,92,3,10,5,0,92,93,
  	5,16,0,0,93,111,1,0,0,0,94,95,5,18,0,0,95,111,3,10,5,6,96,97,5,6,0,0,
  	97,98,5,11,0,0,98,99,3,12,6,0,99,100,5,16,0,0,100,111,1,0,0,0,101,102,
  	5,7,0,0,102,103,5,11,0,0,103,104,3,12,6,0,104,105,5,16,0,0,105,111,1,
  	0,0,0,106,111,5,5,0,0,107,111,5,20,0,0,108,109,5,23,0,0,109,111,6,5,-1,
  	0,110,89,1,0,0,0,110,94,1,0,0,0,110,96,1,0,0,0,110,101,1,0,0,0,110,106,
  	1,0,0,0,110,107,1,0,0,0,110,108,1,0,0,0,111,126,1,0,0,0,112,114,10,9,
  	0,0,113,115,7,2,0,0,114,113,1,0,0,0,114,115,1,0,0,0,115,116,1,0,0,0,116,
  	125,3,10,5,10,117,118,10,8,0,0,118,119,7,1,0,0,119,125,3,10,5,9,120,121,
  	10,10,0,0,121,122,5,14,0,0,122,123,5,5,0,0,123,125,4,5,9,1,124,112,1,
  	0,0,0,124,117,1,0,0,0,124,120,1,0,0,0,125,128,1,0,0,0,126,124,1,0,0,0,
  	126,127,1,0,0,0,127,11,1,0,0,0,128,126,1,0,0,0,129,131,5,18,0,0,130,129,
  	1,0,0,0,130,131,1,0,0,0,131,132,1,0,0,0,132,133,5,5,0,0,133,134,5,4,0,
  	0,134,135,5,5,0,0,135,141,4,6,10,1,136,138,5,18,0,0,137,136,1,0,0,0,137,
  	138,1,0,0,0,138,139,1,0,0,0,139,141,5,5,0,0,140,130,1,0,0,0,140,137,1,
  	0,0,0,141,13,1,0,0,0,142,143,6,7,-1,0,143,144,3,16,8,0,144,150,1,0,0,
  	0,145,146,10,1,0,0,146,147,5,3,0,0,147,149,3,16,8,0,148,145,1,0,0,0,149,
  	152,1,0,0,0,150,148,1,0,0,0,150,151,1,0,0,0,151,15,1,0,0,0,152,150,1,
  	0,0,0,153,154,5,2,0,0,154,155,5,23,0,0,155,156,5,2,0,0,156,157,5,8,0,
  	0,157,158,5,5,0,0,158,159,4,8,12,1,159,17,1,0,0,0,15,23,40,52,54,65,76,
  	84,110,114,124,126,130,137,140,150
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


//----------------- ExtendedDiracContext ------------------------------------------------------------------

ExtendedDiracParser::ExtendedDiracContext::ExtendedDiracContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<ExtendedDiracParser::SetContext *> ExtendedDiracParser::ExtendedDiracContext::set() {
  return getRuleContexts<ExtendedDiracParser::SetContext>();
}

ExtendedDiracParser::SetContext* ExtendedDiracParser::ExtendedDiracContext::set(size_t i) {
  return getRuleContext<ExtendedDiracParser::SetContext>(i);
}

tree::TerminalNode* ExtendedDiracParser::ExtendedDiracContext::SETMINUS() {
  return getToken(ExtendedDiracParser::SETMINUS, 0);
}


size_t ExtendedDiracParser::ExtendedDiracContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleExtendedDirac;
}

void ExtendedDiracParser::ExtendedDiracContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterExtendedDirac(this);
}

void ExtendedDiracParser::ExtendedDiracContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitExtendedDirac(this);
}


std::any ExtendedDiracParser::ExtendedDiracContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitExtendedDirac(this);
  else
    return visitor->visitChildren(this);
}

ExtendedDiracParser::ExtendedDiracContext* ExtendedDiracParser::extendedDirac() {
  ExtendedDiracContext *_localctx = _tracker.createInstance<ExtendedDiracContext>(_ctx, getState());
  enterRule(_localctx, 0, ExtendedDiracParser::RuleExtendedDirac);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(23);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 0, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(18);
      set(0);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(19);
      set(0);
      setState(20);
      match(ExtendedDiracParser::SETMINUS);
      setState(21);
      set(0);
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

//----------------- SetContext ------------------------------------------------------------------

ExtendedDiracParser::SetContext::SetContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* ExtendedDiracParser::SetContext::LEFT_BRACKET() {
  return getToken(ExtendedDiracParser::LEFT_BRACKET, 0);
}

std::vector<ExtendedDiracParser::SetContext *> ExtendedDiracParser::SetContext::set() {
  return getRuleContexts<ExtendedDiracParser::SetContext>();
}

ExtendedDiracParser::SetContext* ExtendedDiracParser::SetContext::set(size_t i) {
  return getRuleContext<ExtendedDiracParser::SetContext>(i);
}

tree::TerminalNode* ExtendedDiracParser::SetContext::RIGHT_BRACKET() {
  return getToken(ExtendedDiracParser::RIGHT_BRACKET, 0);
}

tree::TerminalNode* ExtendedDiracParser::SetContext::LEFT_CURLY_BRACKET() {
  return getToken(ExtendedDiracParser::LEFT_CURLY_BRACKET, 0);
}

ExtendedDiracParser::DiracsContext* ExtendedDiracParser::SetContext::diracs() {
  return getRuleContext<ExtendedDiracParser::DiracsContext>(0);
}

tree::TerminalNode* ExtendedDiracParser::SetContext::RIGHT_CURLY_BRACKET() {
  return getToken(ExtendedDiracParser::RIGHT_CURLY_BRACKET, 0);
}

ExtendedDiracParser::DiracContext* ExtendedDiracParser::SetContext::dirac() {
  return getRuleContext<ExtendedDiracParser::DiracContext>(0);
}

tree::TerminalNode* ExtendedDiracParser::SetContext::BAR() {
  return getToken(ExtendedDiracParser::BAR, 0);
}

ExtendedDiracParser::IjklensContext* ExtendedDiracParser::SetContext::ijklens() {
  return getRuleContext<ExtendedDiracParser::IjklensContext>(0);
}

tree::TerminalNode* ExtendedDiracParser::SetContext::PROD() {
  return getToken(ExtendedDiracParser::PROD, 0);
}

tree::TerminalNode* ExtendedDiracParser::SetContext::UNION() {
  return getToken(ExtendedDiracParser::UNION, 0);
}

tree::TerminalNode* ExtendedDiracParser::SetContext::INTERSECTION() {
  return getToken(ExtendedDiracParser::INTERSECTION, 0);
}

tree::TerminalNode* ExtendedDiracParser::SetContext::POWER() {
  return getToken(ExtendedDiracParser::POWER, 0);
}

tree::TerminalNode* ExtendedDiracParser::SetContext::DIGITS() {
  return getToken(ExtendedDiracParser::DIGITS, 0);
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
  size_t startState = 2;
  enterRecursionRule(_localctx, 2, ExtendedDiracParser::RuleSet, precedence);

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
      setState(26);
      match(ExtendedDiracParser::LEFT_BRACKET);
      setState(27);
      set(0);
      setState(28);
      match(ExtendedDiracParser::RIGHT_BRACKET);
      break;
    }

    case 2: {
      setState(30);
      match(ExtendedDiracParser::LEFT_CURLY_BRACKET);
      setState(31);
      diracs(0);
      setState(32);
      match(ExtendedDiracParser::RIGHT_CURLY_BRACKET);
      break;
    }

    case 3: {
      setState(34);
      match(ExtendedDiracParser::LEFT_CURLY_BRACKET);
      setState(35);
      dirac(0);
      setState(36);
      match(ExtendedDiracParser::BAR);
      setState(37);
      ijklens(0);
      setState(38);
      match(ExtendedDiracParser::RIGHT_CURLY_BRACKET);
      break;
    }

    default:
      break;
    }
    _ctx->stop = _input->LT(-1);
    setState(54);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 3, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        setState(52);
        _errHandler->sync(this);
        switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 2, _ctx)) {
        case 1: {
          _localctx = _tracker.createInstance<SetContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleSet);
          setState(42);

          if (!(precpred(_ctx, 2))) throw FailedPredicateException(this, "precpred(_ctx, 2)");
          setState(43);
          antlrcpp::downCast<SetContext *>(_localctx)->op = match(ExtendedDiracParser::PROD);
          setState(44);
          set(3);
          break;
        }

        case 2: {
          _localctx = _tracker.createInstance<SetContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleSet);
          setState(45);

          if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
          setState(46);
          antlrcpp::downCast<SetContext *>(_localctx)->op = _input->LT(1);
          _la = _input->LA(1);
          if (!(_la == ExtendedDiracParser::INTERSECTION

          || _la == ExtendedDiracParser::UNION)) {
            antlrcpp::downCast<SetContext *>(_localctx)->op = _errHandler->recoverInline(this);
          }
          else {
            _errHandler->reportMatch(this);
            consume();
          }
          setState(47);
          set(2);
          break;
        }

        case 3: {
          _localctx = _tracker.createInstance<SetContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleSet);
          setState(48);

          if (!(precpred(_ctx, 6))) throw FailedPredicateException(this, "precpred(_ctx, 6)");
          setState(49);
          match(ExtendedDiracParser::POWER);
          setState(50);
          antlrcpp::downCast<SetContext *>(_localctx)->n = match(ExtendedDiracParser::DIGITS);
          setState(51);

          if (!(isNonZero((antlrcpp::downCast<SetContext *>(_localctx)->n != nullptr ? antlrcpp::downCast<SetContext *>(_localctx)->n->getText() : "")))) throw FailedPredicateException(this, "isNonZero($n.text)");
          break;
        }

        default:
          break;
        } 
      }
      setState(56);
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
  size_t startState = 4;
  enterRecursionRule(_localctx, 4, ExtendedDiracParser::RuleDiracs, precedence);

    

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
    setState(58);
    dirac(0);
    _ctx->stop = _input->LT(-1);
    setState(65);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 4, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<DiracsContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleDiracs);
        setState(60);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(61);
        match(ExtendedDiracParser::COMMA);
        setState(62);
        dirac(0); 
      }
      setState(67);
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

ExtendedDiracParser::CketContext* ExtendedDiracParser::DiracContext::cket() {
  return getRuleContext<ExtendedDiracParser::CketContext>(0);
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
  size_t startState = 6;
  enterRecursionRule(_localctx, 6, ExtendedDiracParser::RuleDirac, precedence);

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
    setState(69);
    cket();
    _ctx->stop = _input->LT(-1);
    setState(76);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 5, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<DiracContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleDirac);
        setState(71);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(72);
        antlrcpp::downCast<DiracContext *>(_localctx)->op = _input->LT(1);
        _la = _input->LA(1);
        if (!(_la == ExtendedDiracParser::ADD

        || _la == ExtendedDiracParser::SUB)) {
          antlrcpp::downCast<DiracContext *>(_localctx)->op = _errHandler->recoverInline(this);
        }
        else {
          _errHandler->reportMatch(this);
          consume();
        }
        setState(73);
        cket(); 
      }
      setState(78);
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

//----------------- CketContext ------------------------------------------------------------------

ExtendedDiracParser::CketContext::CketContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* ExtendedDiracParser::CketContext::KET() {
  return getToken(ExtendedDiracParser::KET, 0);
}

ExtendedDiracParser::ComplexContext* ExtendedDiracParser::CketContext::complex() {
  return getRuleContext<ExtendedDiracParser::ComplexContext>(0);
}

tree::TerminalNode* ExtendedDiracParser::CketContext::SUB() {
  return getToken(ExtendedDiracParser::SUB, 0);
}

tree::TerminalNode* ExtendedDiracParser::CketContext::MUL() {
  return getToken(ExtendedDiracParser::MUL, 0);
}


size_t ExtendedDiracParser::CketContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleCket;
}

void ExtendedDiracParser::CketContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterCket(this);
}

void ExtendedDiracParser::CketContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitCket(this);
}


std::any ExtendedDiracParser::CketContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitCket(this);
  else
    return visitor->visitChildren(this);
}

ExtendedDiracParser::CketContext* ExtendedDiracParser::cket() {
  CketContext *_localctx = _tracker.createInstance<CketContext>(_ctx, getState());
  enterRule(_localctx, 8, ExtendedDiracParser::RuleCket);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(84);
    _errHandler->sync(this);

    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 6, _ctx)) {
    case 1: {
      setState(79);
      complex(0);
      break;
    }

    case 2: {
      setState(80);
      complex(0);
      setState(81);
      antlrcpp::downCast<CketContext *>(_localctx)->op = match(ExtendedDiracParser::MUL);
      break;
    }

    case 3: {
      setState(83);
      match(ExtendedDiracParser::SUB);
      break;
    }

    default:
      break;
    }
    setState(86);
    antlrcpp::downCast<CketContext *>(_localctx)->ketToken = match(ExtendedDiracParser::KET);

            std::string text = (antlrcpp::downCast<CketContext *>(_localctx)->ketToken != nullptr ? antlrcpp::downCast<CketContext *>(_localctx)->ketToken->getText() : "");           // Get the full text of the KET token
            std::string state = text.substr(1, text.length() - 2); // Remove the first and last characters
        
   
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

tree::TerminalNode* ExtendedDiracParser::ComplexContext::LEFT_BRACKET() {
  return getToken(ExtendedDiracParser::LEFT_BRACKET, 0);
}

std::vector<ExtendedDiracParser::ComplexContext *> ExtendedDiracParser::ComplexContext::complex() {
  return getRuleContexts<ExtendedDiracParser::ComplexContext>();
}

ExtendedDiracParser::ComplexContext* ExtendedDiracParser::ComplexContext::complex(size_t i) {
  return getRuleContext<ExtendedDiracParser::ComplexContext>(i);
}

tree::TerminalNode* ExtendedDiracParser::ComplexContext::RIGHT_BRACKET() {
  return getToken(ExtendedDiracParser::RIGHT_BRACKET, 0);
}

tree::TerminalNode* ExtendedDiracParser::ComplexContext::SUB() {
  return getToken(ExtendedDiracParser::SUB, 0);
}

tree::TerminalNode* ExtendedDiracParser::ComplexContext::EI2PI() {
  return getToken(ExtendedDiracParser::EI2PI, 0);
}

ExtendedDiracParser::AngleContext* ExtendedDiracParser::ComplexContext::angle() {
  return getRuleContext<ExtendedDiracParser::AngleContext>(0);
}

tree::TerminalNode* ExtendedDiracParser::ComplexContext::EIPI() {
  return getToken(ExtendedDiracParser::EIPI, 0);
}

tree::TerminalNode* ExtendedDiracParser::ComplexContext::DIGITS() {
  return getToken(ExtendedDiracParser::DIGITS, 0);
}

tree::TerminalNode* ExtendedDiracParser::ComplexContext::SQRT2() {
  return getToken(ExtendedDiracParser::SQRT2, 0);
}

tree::TerminalNode* ExtendedDiracParser::ComplexContext::NAME() {
  return getToken(ExtendedDiracParser::NAME, 0);
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
  size_t startState = 10;
  enterRecursionRule(_localctx, 10, ExtendedDiracParser::RuleComplex, precedence);

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
    setState(110);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case ExtendedDiracParser::LEFT_BRACKET: {
        setState(90);
        match(ExtendedDiracParser::LEFT_BRACKET);
        setState(91);
        complex(0);
        setState(92);
        match(ExtendedDiracParser::RIGHT_BRACKET);
        break;
      }

      case ExtendedDiracParser::SUB: {
        setState(94);
        match(ExtendedDiracParser::SUB);
        setState(95);
        complex(6);
        break;
      }

      case ExtendedDiracParser::EI2PI: {
        setState(96);
        match(ExtendedDiracParser::EI2PI);
        setState(97);
        match(ExtendedDiracParser::LEFT_BRACKET);
        setState(98);
        angle();
        setState(99);
        match(ExtendedDiracParser::RIGHT_BRACKET);
        break;
      }

      case ExtendedDiracParser::EIPI: {
        setState(101);
        match(ExtendedDiracParser::EIPI);
        setState(102);
        match(ExtendedDiracParser::LEFT_BRACKET);
        setState(103);
        angle();
        setState(104);
        match(ExtendedDiracParser::RIGHT_BRACKET);
        break;
      }

      case ExtendedDiracParser::DIGITS: {
        setState(106);
        match(ExtendedDiracParser::DIGITS);
        break;
      }

      case ExtendedDiracParser::SQRT2: {
        setState(107);
        match(ExtendedDiracParser::SQRT2);
        break;
      }

      case ExtendedDiracParser::NAME: {
        setState(108);
        antlrcpp::downCast<ComplexContext *>(_localctx)->var = match(ExtendedDiracParser::NAME);
         if (!predefinedVars.contains((antlrcpp::downCast<ComplexContext *>(_localctx)->var != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->var->getText() : ""))) isSymbolicAutomaton = true; 
        break;
      }

    default:
      throw NoViableAltException(this);
    }
    _ctx->stop = _input->LT(-1);
    setState(126);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 10, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        setState(124);
        _errHandler->sync(this);
        switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 9, _ctx)) {
        case 1: {
          _localctx = _tracker.createInstance<ComplexContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleComplex);
          setState(112);

          if (!(precpred(_ctx, 9))) throw FailedPredicateException(this, "precpred(_ctx, 9)");
          setState(114);
          _errHandler->sync(this);

          _la = _input->LA(1);
          if (_la == ExtendedDiracParser::DIV

          || _la == ExtendedDiracParser::MUL) {
            setState(113);
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
          }
          setState(116);
          complex(10);
          break;
        }

        case 2: {
          _localctx = _tracker.createInstance<ComplexContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleComplex);
          setState(117);

          if (!(precpred(_ctx, 8))) throw FailedPredicateException(this, "precpred(_ctx, 8)");
          setState(118);
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
          setState(119);
          complex(9);
          break;
        }

        case 3: {
          _localctx = _tracker.createInstance<ComplexContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleComplex);
          setState(120);

          if (!(precpred(_ctx, 10))) throw FailedPredicateException(this, "precpred(_ctx, 10)");
          setState(121);
          match(ExtendedDiracParser::POWER);
          setState(122);
          antlrcpp::downCast<ComplexContext *>(_localctx)->n = match(ExtendedDiracParser::DIGITS);
          setState(123);

          if (!(isNonZero((antlrcpp::downCast<ComplexContext *>(_localctx)->n != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->n->getText() : "")))) throw FailedPredicateException(this, "isNonZero($n.text)");
          break;
        }

        default:
          break;
        } 
      }
      setState(128);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 10, _ctx);
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

std::vector<tree::TerminalNode *> ExtendedDiracParser::AngleContext::DIGITS() {
  return getTokens(ExtendedDiracParser::DIGITS);
}

tree::TerminalNode* ExtendedDiracParser::AngleContext::DIGITS(size_t i) {
  return getToken(ExtendedDiracParser::DIGITS, i);
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
  enterRule(_localctx, 12, ExtendedDiracParser::RuleAngle);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(140);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 13, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(130);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == ExtendedDiracParser::SUB) {
        setState(129);
        match(ExtendedDiracParser::SUB);
      }
      setState(132);
      antlrcpp::downCast<AngleContext *>(_localctx)->x = match(ExtendedDiracParser::DIGITS);
      setState(133);
      match(ExtendedDiracParser::DIV);
      setState(134);
      antlrcpp::downCast<AngleContext *>(_localctx)->y = match(ExtendedDiracParser::DIGITS);
      setState(135);

      if (!(isNonZero((antlrcpp::downCast<AngleContext *>(_localctx)->y != nullptr ? antlrcpp::downCast<AngleContext *>(_localctx)->y->getText() : "")))) throw FailedPredicateException(this, "isNonZero($y.text)");
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(137);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == ExtendedDiracParser::SUB) {
        setState(136);
        match(ExtendedDiracParser::SUB);
      }
      setState(139);
      antlrcpp::downCast<AngleContext *>(_localctx)->n = match(ExtendedDiracParser::DIGITS);
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

//----------------- IjklensContext ------------------------------------------------------------------

ExtendedDiracParser::IjklensContext::IjklensContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

ExtendedDiracParser::IjklenContext* ExtendedDiracParser::IjklensContext::ijklen() {
  return getRuleContext<ExtendedDiracParser::IjklenContext>(0);
}

ExtendedDiracParser::IjklensContext* ExtendedDiracParser::IjklensContext::ijklens() {
  return getRuleContext<ExtendedDiracParser::IjklensContext>(0);
}

tree::TerminalNode* ExtendedDiracParser::IjklensContext::COMMA() {
  return getToken(ExtendedDiracParser::COMMA, 0);
}


size_t ExtendedDiracParser::IjklensContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleIjklens;
}

void ExtendedDiracParser::IjklensContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterIjklens(this);
}

void ExtendedDiracParser::IjklensContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitIjklens(this);
}


std::any ExtendedDiracParser::IjklensContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitIjklens(this);
  else
    return visitor->visitChildren(this);
}


ExtendedDiracParser::IjklensContext* ExtendedDiracParser::ijklens() {
   return ijklens(0);
}

ExtendedDiracParser::IjklensContext* ExtendedDiracParser::ijklens(int precedence) {
  ParserRuleContext *parentContext = _ctx;
  size_t parentState = getState();
  ExtendedDiracParser::IjklensContext *_localctx = _tracker.createInstance<IjklensContext>(_ctx, parentState);
  ExtendedDiracParser::IjklensContext *previousContext = _localctx;
  (void)previousContext; // Silence compiler, in case the context is not used by generated code.
  size_t startState = 14;
  enterRecursionRule(_localctx, 14, ExtendedDiracParser::RuleIjklens, precedence);

    

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
    setState(143);
    ijklen();
    _ctx->stop = _input->LT(-1);
    setState(150);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 14, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<IjklensContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleIjklens);
        setState(145);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(146);
        match(ExtendedDiracParser::COMMA);
        setState(147);
        ijklen(); 
      }
      setState(152);
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

//----------------- IjklenContext ------------------------------------------------------------------

ExtendedDiracParser::IjklenContext::IjklenContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<tree::TerminalNode *> ExtendedDiracParser::IjklenContext::BAR() {
  return getTokens(ExtendedDiracParser::BAR);
}

tree::TerminalNode* ExtendedDiracParser::IjklenContext::BAR(size_t i) {
  return getToken(ExtendedDiracParser::BAR, i);
}

tree::TerminalNode* ExtendedDiracParser::IjklenContext::EQ() {
  return getToken(ExtendedDiracParser::EQ, 0);
}

tree::TerminalNode* ExtendedDiracParser::IjklenContext::NAME() {
  return getToken(ExtendedDiracParser::NAME, 0);
}

tree::TerminalNode* ExtendedDiracParser::IjklenContext::DIGITS() {
  return getToken(ExtendedDiracParser::DIGITS, 0);
}


size_t ExtendedDiracParser::IjklenContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleIjklen;
}

void ExtendedDiracParser::IjklenContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterIjklen(this);
}

void ExtendedDiracParser::IjklenContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitIjklen(this);
}


std::any ExtendedDiracParser::IjklenContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitIjklen(this);
  else
    return visitor->visitChildren(this);
}

ExtendedDiracParser::IjklenContext* ExtendedDiracParser::ijklen() {
  IjklenContext *_localctx = _tracker.createInstance<IjklenContext>(_ctx, getState());
  enterRule(_localctx, 16, ExtendedDiracParser::RuleIjklen);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(153);
    match(ExtendedDiracParser::BAR);
    setState(154);
    antlrcpp::downCast<IjklenContext *>(_localctx)->var = match(ExtendedDiracParser::NAME);
    setState(155);
    match(ExtendedDiracParser::BAR);
    setState(156);
    match(ExtendedDiracParser::EQ);
    setState(157);
    antlrcpp::downCast<IjklenContext *>(_localctx)->len = match(ExtendedDiracParser::DIGITS);
    setState(158);

    if (!(isASingleLetter((antlrcpp::downCast<IjklenContext *>(_localctx)->var != nullptr ? antlrcpp::downCast<IjklenContext *>(_localctx)->var->getText() : "")) && isNonZero((antlrcpp::downCast<IjklenContext *>(_localctx)->len != nullptr ? antlrcpp::downCast<IjklenContext *>(_localctx)->len->getText() : "")))) throw FailedPredicateException(this, "isASingleLetter($var.text) && isNonZero($len.text)");
   
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
    case 1: return setSempred(antlrcpp::downCast<SetContext *>(context), predicateIndex);
    case 2: return diracsSempred(antlrcpp::downCast<DiracsContext *>(context), predicateIndex);
    case 3: return diracSempred(antlrcpp::downCast<DiracContext *>(context), predicateIndex);
    case 5: return complexSempred(antlrcpp::downCast<ComplexContext *>(context), predicateIndex);
    case 6: return angleSempred(antlrcpp::downCast<AngleContext *>(context), predicateIndex);
    case 7: return ijklensSempred(antlrcpp::downCast<IjklensContext *>(context), predicateIndex);
    case 8: return ijklenSempred(antlrcpp::downCast<IjklenContext *>(context), predicateIndex);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::setSempred(SetContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 0: return precpred(_ctx, 2);
    case 1: return precpred(_ctx, 1);
    case 2: return precpred(_ctx, 6);
    case 3: return isNonZero((antlrcpp::downCast<SetContext *>(_localctx)->n != nullptr ? antlrcpp::downCast<SetContext *>(_localctx)->n->getText() : ""));

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
    case 6: return precpred(_ctx, 9);
    case 7: return precpred(_ctx, 8);
    case 8: return precpred(_ctx, 10);
    case 9: return isNonZero((antlrcpp::downCast<ComplexContext *>(_localctx)->n != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->n->getText() : ""));

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::angleSempred(AngleContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 10: return isNonZero((antlrcpp::downCast<AngleContext *>(_localctx)->y != nullptr ? antlrcpp::downCast<AngleContext *>(_localctx)->y->getText() : ""));

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::ijklensSempred(IjklensContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 11: return precpred(_ctx, 1);

  default:
    break;
  }
  return true;
}

bool ExtendedDiracParser::ijklenSempred(IjklenContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 12: return isASingleLetter((antlrcpp::downCast<IjklenContext *>(_localctx)->var != nullptr ? antlrcpp::downCast<IjklenContext *>(_localctx)->var->getText() : "")) && isNonZero((antlrcpp::downCast<IjklenContext *>(_localctx)->len != nullptr ? antlrcpp::downCast<IjklenContext *>(_localctx)->len->getText() : ""));

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
