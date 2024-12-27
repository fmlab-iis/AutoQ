
// Generated from src/ExtendedDirac/ExtendedDirac.g4 by ANTLR 4.13.2


#include "ExtendedDiracListener.h"
#include "ExtendedDiracVisitor.h"

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

::antlr4::internal::OnceFlag extendeddiracParserOnceFlag;
#if ANTLR4_USE_THREAD_LOCAL_CACHE
static thread_local
#endif
std::unique_ptr<ExtendedDiracParserStaticData> extendeddiracParserStaticData = nullptr;

void extendeddiracParserInitialize() {
#if ANTLR4_USE_THREAD_LOCAL_CACHE
  if (extendeddiracParserStaticData != nullptr) {
    return;
  }
#else
  assert(extendeddiracParserStaticData == nullptr);
#endif
  auto staticData = std::make_unique<ExtendedDiracParserStaticData>(
    std::vector<std::string>{
      "extendedDirac", "set", "diracs", "dirac", "cket", "complex", "angle", 
      "ijklens", "ijklen"
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
  	4,1,23,158,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,6,2,
  	7,7,7,2,8,7,8,1,0,1,0,1,0,1,0,1,0,3,0,24,8,0,1,1,1,1,1,1,1,1,1,1,1,1,
  	1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,3,1,41,8,1,1,1,1,1,1,1,1,1,1,1,1,
  	1,1,1,1,1,1,1,1,1,5,1,53,8,1,10,1,12,1,56,9,1,1,2,1,2,1,2,1,2,1,2,1,2,
  	5,2,64,8,2,10,2,12,2,67,9,2,1,3,1,3,1,3,1,3,1,3,1,3,5,3,75,8,3,10,3,12,
  	3,78,9,3,1,4,1,4,1,4,1,4,1,4,3,4,85,8,4,1,4,1,4,1,4,1,5,1,5,1,5,1,5,1,
  	5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,3,5,109,8,5,
  	1,5,1,5,3,5,113,8,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,5,5,123,8,5,10,5,
  	12,5,126,9,5,1,6,3,6,129,8,6,1,6,1,6,1,6,1,6,1,6,3,6,136,8,6,1,6,3,6,
  	139,8,6,1,7,1,7,1,7,1,7,1,7,1,7,5,7,147,8,7,10,7,12,7,150,9,7,1,8,1,8,
  	1,8,1,8,1,8,1,8,1,8,0,5,2,4,6,10,14,9,0,2,4,6,8,10,12,14,16,0,3,2,0,16,
  	16,22,22,2,0,13,13,21,21,2,0,14,14,18,18,173,0,23,1,0,0,0,2,40,1,0,0,
  	0,4,57,1,0,0,0,6,68,1,0,0,0,8,84,1,0,0,0,10,108,1,0,0,0,12,138,1,0,0,
  	0,14,140,1,0,0,0,16,151,1,0,0,0,18,24,3,2,1,0,19,20,3,2,1,0,20,21,5,1,
  	0,0,21,22,3,2,1,0,22,24,1,0,0,0,23,18,1,0,0,0,23,19,1,0,0,0,24,1,1,0,
  	0,0,25,26,6,1,-1,0,26,27,5,3,0,0,27,28,3,2,1,0,28,29,5,4,0,0,29,41,1,
  	0,0,0,30,31,5,5,0,0,31,32,3,4,2,0,32,33,5,6,0,0,33,41,1,0,0,0,34,35,5,
  	5,0,0,35,36,3,6,3,0,36,37,5,7,0,0,37,38,3,14,7,0,38,39,5,6,0,0,39,41,
  	1,0,0,0,40,25,1,0,0,0,40,30,1,0,0,0,40,34,1,0,0,0,41,54,1,0,0,0,42,43,
  	10,2,0,0,43,44,5,20,0,0,44,53,3,2,1,3,45,46,10,1,0,0,46,47,7,0,0,0,47,
  	53,3,2,1,2,48,49,10,6,0,0,49,50,5,2,0,0,50,51,5,15,0,0,51,53,4,1,3,1,
  	52,42,1,0,0,0,52,45,1,0,0,0,52,48,1,0,0,0,53,56,1,0,0,0,54,52,1,0,0,0,
  	54,55,1,0,0,0,55,3,1,0,0,0,56,54,1,0,0,0,57,58,6,2,-1,0,58,59,3,6,3,0,
  	59,65,1,0,0,0,60,61,10,1,0,0,61,62,5,8,0,0,62,64,3,6,3,0,63,60,1,0,0,
  	0,64,67,1,0,0,0,65,63,1,0,0,0,65,66,1,0,0,0,66,5,1,0,0,0,67,65,1,0,0,
  	0,68,69,6,3,-1,0,69,70,3,8,4,0,70,76,1,0,0,0,71,72,10,1,0,0,72,73,7,1,
  	0,0,73,75,3,8,4,0,74,71,1,0,0,0,75,78,1,0,0,0,76,74,1,0,0,0,76,77,1,0,
  	0,0,77,7,1,0,0,0,78,76,1,0,0,0,79,85,3,10,5,0,80,81,3,10,5,0,81,82,5,
  	18,0,0,82,85,1,0,0,0,83,85,5,21,0,0,84,79,1,0,0,0,84,80,1,0,0,0,84,83,
  	1,0,0,0,84,85,1,0,0,0,85,86,1,0,0,0,86,87,5,17,0,0,87,88,6,4,-1,0,88,
  	9,1,0,0,0,89,90,6,5,-1,0,90,91,5,3,0,0,91,92,3,10,5,0,92,93,5,4,0,0,93,
  	109,1,0,0,0,94,95,5,21,0,0,95,109,3,10,5,6,96,97,5,9,0,0,97,98,3,12,6,
  	0,98,99,5,4,0,0,99,109,1,0,0,0,100,101,5,10,0,0,101,102,3,12,6,0,102,
  	103,5,4,0,0,103,109,1,0,0,0,104,109,5,15,0,0,105,109,5,11,0,0,106,107,
  	5,19,0,0,107,109,6,5,-1,0,108,89,1,0,0,0,108,94,1,0,0,0,108,96,1,0,0,
  	0,108,100,1,0,0,0,108,104,1,0,0,0,108,105,1,0,0,0,108,106,1,0,0,0,109,
  	124,1,0,0,0,110,112,10,9,0,0,111,113,7,2,0,0,112,111,1,0,0,0,112,113,
  	1,0,0,0,113,114,1,0,0,0,114,123,3,10,5,10,115,116,10,8,0,0,116,117,7,
  	1,0,0,117,123,3,10,5,9,118,119,10,10,0,0,119,120,5,2,0,0,120,121,5,15,
  	0,0,121,123,4,5,9,1,122,110,1,0,0,0,122,115,1,0,0,0,122,118,1,0,0,0,123,
  	126,1,0,0,0,124,122,1,0,0,0,124,125,1,0,0,0,125,11,1,0,0,0,126,124,1,
  	0,0,0,127,129,5,21,0,0,128,127,1,0,0,0,128,129,1,0,0,0,129,130,1,0,0,
  	0,130,131,5,15,0,0,131,132,5,14,0,0,132,133,5,15,0,0,133,139,4,6,10,1,
  	134,136,5,21,0,0,135,134,1,0,0,0,135,136,1,0,0,0,136,137,1,0,0,0,137,
  	139,5,15,0,0,138,128,1,0,0,0,138,135,1,0,0,0,139,13,1,0,0,0,140,141,6,
  	7,-1,0,141,142,3,16,8,0,142,148,1,0,0,0,143,144,10,1,0,0,144,145,5,8,
  	0,0,145,147,3,16,8,0,146,143,1,0,0,0,147,150,1,0,0,0,148,146,1,0,0,0,
  	148,149,1,0,0,0,149,15,1,0,0,0,150,148,1,0,0,0,151,152,5,7,0,0,152,153,
  	5,19,0,0,153,154,5,12,0,0,154,155,5,15,0,0,155,156,4,8,12,1,156,17,1,
  	0,0,0,15,23,40,52,54,65,76,84,108,112,122,124,128,135,138,148
  };
  staticData->serializedATN = antlr4::atn::SerializedATNView(serializedATNSegment, sizeof(serializedATNSegment) / sizeof(serializedATNSegment[0]));

  antlr4::atn::ATNDeserializer deserializer;
  staticData->atn = deserializer.deserialize(staticData->serializedATN);

  const size_t count = staticData->atn->getNumberOfDecisions();
  staticData->decisionToDFA.reserve(count);
  for (size_t i = 0; i < count; i++) { 
    staticData->decisionToDFA.emplace_back(staticData->atn->getDecisionState(i), i);
  }
  extendeddiracParserStaticData = std::move(staticData);
}

}

ExtendedDiracParser::ExtendedDiracParser(TokenStream *input) : ExtendedDiracParser(input, antlr4::atn::ParserATNSimulatorOptions()) {}

ExtendedDiracParser::ExtendedDiracParser(TokenStream *input, const antlr4::atn::ParserATNSimulatorOptions &options) : Parser(input) {
  ExtendedDiracParser::initialize();
  _interpreter = new atn::ParserATNSimulator(this, *extendeddiracParserStaticData->atn, extendeddiracParserStaticData->decisionToDFA, extendeddiracParserStaticData->sharedContextCache, options);
}

ExtendedDiracParser::~ExtendedDiracParser() {
  delete _interpreter;
}

const atn::ATN& ExtendedDiracParser::getATN() const {
  return *extendeddiracParserStaticData->atn;
}

std::string ExtendedDiracParser::getGrammarFileName() const {
  return "ExtendedDirac.g4";
}

const std::vector<std::string>& ExtendedDiracParser::getRuleNames() const {
  return extendeddiracParserStaticData->ruleNames;
}

const dfa::Vocabulary& ExtendedDiracParser::getVocabulary() const {
  return extendeddiracParserStaticData->vocabulary;
}

antlr4::atn::SerializedATNView ExtendedDiracParser::getSerializedATN() const {
  return extendeddiracParserStaticData->serializedATN;
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


size_t ExtendedDiracParser::ExtendedDiracContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleExtendedDirac;
}

void ExtendedDiracParser::ExtendedDiracContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterExtendedDirac(this);
}

void ExtendedDiracParser::ExtendedDiracContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitExtendedDirac(this);
}


std::any ExtendedDiracParser::ExtendedDiracContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracVisitor*>(visitor))
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
      match(ExtendedDiracParser::T__0);
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

std::vector<ExtendedDiracParser::SetContext *> ExtendedDiracParser::SetContext::set() {
  return getRuleContexts<ExtendedDiracParser::SetContext>();
}

ExtendedDiracParser::SetContext* ExtendedDiracParser::SetContext::set(size_t i) {
  return getRuleContext<ExtendedDiracParser::SetContext>(i);
}

ExtendedDiracParser::DiracsContext* ExtendedDiracParser::SetContext::diracs() {
  return getRuleContext<ExtendedDiracParser::DiracsContext>(0);
}

ExtendedDiracParser::DiracContext* ExtendedDiracParser::SetContext::dirac() {
  return getRuleContext<ExtendedDiracParser::DiracContext>(0);
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

tree::TerminalNode* ExtendedDiracParser::SetContext::DIGITS() {
  return getToken(ExtendedDiracParser::DIGITS, 0);
}


size_t ExtendedDiracParser::SetContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleSet;
}

void ExtendedDiracParser::SetContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSet(this);
}

void ExtendedDiracParser::SetContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSet(this);
}


std::any ExtendedDiracParser::SetContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracVisitor*>(visitor))
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
      match(ExtendedDiracParser::T__2);
      setState(27);
      set(0);
      setState(28);
      match(ExtendedDiracParser::T__3);
      break;
    }

    case 2: {
      setState(30);
      match(ExtendedDiracParser::T__4);
      setState(31);
      diracs(0);
      setState(32);
      match(ExtendedDiracParser::T__5);
      break;
    }

    case 3: {
      setState(34);
      match(ExtendedDiracParser::T__4);
      setState(35);
      dirac(0);
      setState(36);
      match(ExtendedDiracParser::T__6);
      setState(37);
      ijklens(0);
      setState(38);
      match(ExtendedDiracParser::T__5);
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
          match(ExtendedDiracParser::T__1);
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


size_t ExtendedDiracParser::DiracsContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleDiracs;
}

void ExtendedDiracParser::DiracsContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDiracs(this);
}

void ExtendedDiracParser::DiracsContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDiracs(this);
}


std::any ExtendedDiracParser::DiracsContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracVisitor*>(visitor))
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
        match(ExtendedDiracParser::T__7);
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
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDirac(this);
}

void ExtendedDiracParser::DiracContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDirac(this);
}


std::any ExtendedDiracParser::DiracContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracVisitor*>(visitor))
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
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterCket(this);
}

void ExtendedDiracParser::CketContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitCket(this);
}


std::any ExtendedDiracParser::CketContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracVisitor*>(visitor))
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

std::vector<ExtendedDiracParser::ComplexContext *> ExtendedDiracParser::ComplexContext::complex() {
  return getRuleContexts<ExtendedDiracParser::ComplexContext>();
}

ExtendedDiracParser::ComplexContext* ExtendedDiracParser::ComplexContext::complex(size_t i) {
  return getRuleContext<ExtendedDiracParser::ComplexContext>(i);
}

tree::TerminalNode* ExtendedDiracParser::ComplexContext::SUB() {
  return getToken(ExtendedDiracParser::SUB, 0);
}

ExtendedDiracParser::AngleContext* ExtendedDiracParser::ComplexContext::angle() {
  return getRuleContext<ExtendedDiracParser::AngleContext>(0);
}

tree::TerminalNode* ExtendedDiracParser::ComplexContext::DIGITS() {
  return getToken(ExtendedDiracParser::DIGITS, 0);
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


size_t ExtendedDiracParser::ComplexContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleComplex;
}

void ExtendedDiracParser::ComplexContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterComplex(this);
}

void ExtendedDiracParser::ComplexContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitComplex(this);
}


std::any ExtendedDiracParser::ComplexContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracVisitor*>(visitor))
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
    setState(108);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case ExtendedDiracParser::T__2: {
        setState(90);
        match(ExtendedDiracParser::T__2);
        setState(91);
        complex(0);
        setState(92);
        match(ExtendedDiracParser::T__3);
        break;
      }

      case ExtendedDiracParser::SUB: {
        setState(94);
        match(ExtendedDiracParser::SUB);
        setState(95);
        complex(6);
        break;
      }

      case ExtendedDiracParser::T__8: {
        setState(96);
        match(ExtendedDiracParser::T__8);
        setState(97);
        angle();
        setState(98);
        match(ExtendedDiracParser::T__3);
        break;
      }

      case ExtendedDiracParser::T__9: {
        setState(100);
        match(ExtendedDiracParser::T__9);
        setState(101);
        angle();
        setState(102);
        match(ExtendedDiracParser::T__3);
        break;
      }

      case ExtendedDiracParser::DIGITS: {
        setState(104);
        match(ExtendedDiracParser::DIGITS);
        break;
      }

      case ExtendedDiracParser::T__10: {
        setState(105);
        match(ExtendedDiracParser::T__10);
        break;
      }

      case ExtendedDiracParser::NAME: {
        setState(106);
        antlrcpp::downCast<ComplexContext *>(_localctx)->var = match(ExtendedDiracParser::NAME);
         if (!predefinedVars.contains((antlrcpp::downCast<ComplexContext *>(_localctx)->var != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->var->getText() : ""))) isSymbolicAutomaton = true; 
        break;
      }

    default:
      throw NoViableAltException(this);
    }
    _ctx->stop = _input->LT(-1);
    setState(124);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 10, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        setState(122);
        _errHandler->sync(this);
        switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 9, _ctx)) {
        case 1: {
          _localctx = _tracker.createInstance<ComplexContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleComplex);
          setState(110);

          if (!(precpred(_ctx, 9))) throw FailedPredicateException(this, "precpred(_ctx, 9)");
          setState(112);
          _errHandler->sync(this);

          _la = _input->LA(1);
          if (_la == ExtendedDiracParser::DIV

          || _la == ExtendedDiracParser::MUL) {
            setState(111);
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
          setState(114);
          complex(10);
          break;
        }

        case 2: {
          _localctx = _tracker.createInstance<ComplexContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleComplex);
          setState(115);

          if (!(precpred(_ctx, 8))) throw FailedPredicateException(this, "precpred(_ctx, 8)");
          setState(116);
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
          setState(117);
          complex(9);
          break;
        }

        case 3: {
          _localctx = _tracker.createInstance<ComplexContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleComplex);
          setState(118);

          if (!(precpred(_ctx, 10))) throw FailedPredicateException(this, "precpred(_ctx, 10)");
          setState(119);
          match(ExtendedDiracParser::T__1);
          setState(120);
          antlrcpp::downCast<ComplexContext *>(_localctx)->n = match(ExtendedDiracParser::DIGITS);
          setState(121);

          if (!(isNonZero((antlrcpp::downCast<ComplexContext *>(_localctx)->n != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->n->getText() : "")))) throw FailedPredicateException(this, "isNonZero($n.text)");
          break;
        }

        default:
          break;
        } 
      }
      setState(126);
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
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterAngle(this);
}

void ExtendedDiracParser::AngleContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitAngle(this);
}


std::any ExtendedDiracParser::AngleContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracVisitor*>(visitor))
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
    setState(138);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 13, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(128);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == ExtendedDiracParser::SUB) {
        setState(127);
        match(ExtendedDiracParser::SUB);
      }
      setState(130);
      antlrcpp::downCast<AngleContext *>(_localctx)->x = match(ExtendedDiracParser::DIGITS);
      setState(131);
      match(ExtendedDiracParser::DIV);
      setState(132);
      antlrcpp::downCast<AngleContext *>(_localctx)->y = match(ExtendedDiracParser::DIGITS);
      setState(133);

      if (!(isNonZero((antlrcpp::downCast<AngleContext *>(_localctx)->y != nullptr ? antlrcpp::downCast<AngleContext *>(_localctx)->y->getText() : "")))) throw FailedPredicateException(this, "isNonZero($y.text)");
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(135);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == ExtendedDiracParser::SUB) {
        setState(134);
        match(ExtendedDiracParser::SUB);
      }
      setState(137);
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


size_t ExtendedDiracParser::IjklensContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleIjklens;
}

void ExtendedDiracParser::IjklensContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterIjklens(this);
}

void ExtendedDiracParser::IjklensContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitIjklens(this);
}


std::any ExtendedDiracParser::IjklensContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracVisitor*>(visitor))
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
    setState(141);
    ijklen();
    _ctx->stop = _input->LT(-1);
    setState(148);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 14, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<IjklensContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleIjklens);
        setState(143);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(144);
        match(ExtendedDiracParser::T__7);
        setState(145);
        ijklen(); 
      }
      setState(150);
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
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterIjklen(this);
}

void ExtendedDiracParser::IjklenContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitIjklen(this);
}


std::any ExtendedDiracParser::IjklenContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracVisitor*>(visitor))
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
    setState(151);
    match(ExtendedDiracParser::T__6);
    setState(152);
    antlrcpp::downCast<IjklenContext *>(_localctx)->var = match(ExtendedDiracParser::NAME);
    setState(153);
    match(ExtendedDiracParser::T__11);
    setState(154);
    antlrcpp::downCast<IjklenContext *>(_localctx)->len = match(ExtendedDiracParser::DIGITS);
    setState(155);

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
  extendeddiracParserInitialize();
#else
  ::antlr4::internal::call_once(extendeddiracParserOnceFlag, extendeddiracParserInitialize);
#endif
}
