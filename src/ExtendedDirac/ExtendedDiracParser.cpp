
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
      "extendedDirac", "muloperators", "muloperator", "accepted", "set", 
      "diracs", "dirac", "cket", "complex", "angle", "ijklens", "ijklen"
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
  	4,1,25,187,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,6,2,
  	7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,2,11,7,11,1,0,1,0,1,0,1,0,3,0,29,8,0,
  	1,0,1,0,1,1,4,1,34,8,1,11,1,12,1,35,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,3,1,
  	3,1,3,1,3,1,3,3,3,50,8,3,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,
  	1,4,1,4,1,4,1,4,3,4,67,8,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,5,
  	4,79,8,4,10,4,12,4,82,9,4,1,5,1,5,1,5,1,5,1,5,1,5,5,5,90,8,5,10,5,12,
  	5,93,9,5,1,6,1,6,1,6,1,6,1,6,1,6,5,6,101,8,6,10,6,12,6,104,9,6,1,7,1,
  	7,1,7,1,7,1,7,3,7,111,8,7,1,7,1,7,1,7,1,8,1,8,1,8,1,8,1,8,1,8,1,8,1,8,
  	1,8,1,8,1,8,1,8,1,8,1,8,1,8,1,8,1,8,1,8,1,8,1,8,1,8,3,8,137,8,8,1,8,1,
  	8,3,8,141,8,8,1,8,1,8,1,8,1,8,1,8,1,8,1,8,1,8,5,8,151,8,8,10,8,12,8,154,
  	9,8,1,9,3,9,157,8,9,1,9,1,9,1,9,1,9,1,9,3,9,164,8,9,1,9,3,9,167,8,9,1,
  	10,1,10,1,10,1,10,1,10,1,10,5,10,175,8,10,10,10,12,10,178,9,10,1,11,1,
  	11,1,11,1,11,1,11,1,11,1,11,1,11,0,5,8,10,12,16,20,12,0,2,4,6,8,10,12,
  	14,16,18,20,22,0,4,1,1,14,14,2,0,9,9,22,22,2,0,1,1,19,19,2,0,4,4,13,13,
  	201,0,24,1,0,0,0,2,33,1,0,0,0,4,37,1,0,0,0,6,49,1,0,0,0,8,66,1,0,0,0,
  	10,83,1,0,0,0,12,94,1,0,0,0,14,110,1,0,0,0,16,136,1,0,0,0,18,166,1,0,
  	0,0,20,168,1,0,0,0,22,179,1,0,0,0,24,28,3,6,3,0,25,26,5,23,0,0,26,27,
  	5,14,0,0,27,29,3,2,1,0,28,25,1,0,0,0,28,29,1,0,0,0,29,30,1,0,0,0,30,31,
  	5,0,0,1,31,1,1,0,0,0,32,34,3,4,2,0,33,32,1,0,0,0,34,35,1,0,0,0,35,33,
  	1,0,0,0,35,36,1,0,0,0,36,3,1,0,0,0,37,38,3,16,8,0,38,39,5,16,0,0,39,40,
  	3,16,8,0,40,41,5,8,0,0,41,42,3,16,8,0,42,43,7,0,0,0,43,5,1,0,0,0,44,50,
  	3,8,4,0,45,46,3,8,4,0,46,47,5,20,0,0,47,48,3,8,4,0,48,50,1,0,0,0,49,44,
  	1,0,0,0,49,45,1,0,0,0,50,7,1,0,0,0,51,52,6,4,-1,0,52,53,5,11,0,0,53,54,
  	3,8,4,0,54,55,5,17,0,0,55,67,1,0,0,0,56,57,5,12,0,0,57,58,3,10,5,0,58,
  	59,5,18,0,0,59,67,1,0,0,0,60,61,5,12,0,0,61,62,3,12,6,0,62,63,5,2,0,0,
  	63,64,3,20,10,0,64,65,5,18,0,0,65,67,1,0,0,0,66,51,1,0,0,0,66,56,1,0,
  	0,0,66,60,1,0,0,0,67,80,1,0,0,0,68,69,10,2,0,0,69,70,5,16,0,0,70,79,3,
  	8,4,3,71,72,10,1,0,0,72,73,7,1,0,0,73,79,3,8,4,2,74,75,10,6,0,0,75,76,
  	5,15,0,0,76,77,5,5,0,0,77,79,4,4,3,1,78,68,1,0,0,0,78,71,1,0,0,0,78,74,
  	1,0,0,0,79,82,1,0,0,0,80,78,1,0,0,0,80,81,1,0,0,0,81,9,1,0,0,0,82,80,
  	1,0,0,0,83,84,6,5,-1,0,84,85,3,12,6,0,85,91,1,0,0,0,86,87,10,1,0,0,87,
  	88,5,3,0,0,88,90,3,12,6,0,89,86,1,0,0,0,90,93,1,0,0,0,91,89,1,0,0,0,91,
  	92,1,0,0,0,92,11,1,0,0,0,93,91,1,0,0,0,94,95,6,6,-1,0,95,96,3,14,7,0,
  	96,102,1,0,0,0,97,98,10,1,0,0,98,99,7,2,0,0,99,101,3,14,7,0,100,97,1,
  	0,0,0,101,104,1,0,0,0,102,100,1,0,0,0,102,103,1,0,0,0,103,13,1,0,0,0,
  	104,102,1,0,0,0,105,111,3,16,8,0,106,107,3,16,8,0,107,108,5,13,0,0,108,
  	111,1,0,0,0,109,111,5,19,0,0,110,105,1,0,0,0,110,106,1,0,0,0,110,109,
  	1,0,0,0,110,111,1,0,0,0,111,112,1,0,0,0,112,113,5,10,0,0,113,114,6,7,
  	-1,0,114,15,1,0,0,0,115,116,6,8,-1,0,116,117,5,11,0,0,117,118,3,16,8,
  	0,118,119,5,17,0,0,119,137,1,0,0,0,120,121,5,19,0,0,121,137,3,16,8,6,
  	122,123,5,6,0,0,123,124,5,11,0,0,124,125,3,18,9,0,125,126,5,17,0,0,126,
  	137,1,0,0,0,127,128,5,7,0,0,128,129,5,11,0,0,129,130,3,18,9,0,130,131,
  	5,17,0,0,131,137,1,0,0,0,132,137,5,5,0,0,133,137,5,21,0,0,134,135,5,25,
  	0,0,135,137,6,8,-1,0,136,115,1,0,0,0,136,120,1,0,0,0,136,122,1,0,0,0,
  	136,127,1,0,0,0,136,132,1,0,0,0,136,133,1,0,0,0,136,134,1,0,0,0,137,152,
  	1,0,0,0,138,140,10,9,0,0,139,141,7,3,0,0,140,139,1,0,0,0,140,141,1,0,
  	0,0,141,142,1,0,0,0,142,151,3,16,8,10,143,144,10,8,0,0,144,145,7,2,0,
  	0,145,151,3,16,8,9,146,147,10,10,0,0,147,148,5,15,0,0,148,149,5,5,0,0,
  	149,151,4,8,9,1,150,138,1,0,0,0,150,143,1,0,0,0,150,146,1,0,0,0,151,154,
  	1,0,0,0,152,150,1,0,0,0,152,153,1,0,0,0,153,17,1,0,0,0,154,152,1,0,0,
  	0,155,157,5,19,0,0,156,155,1,0,0,0,156,157,1,0,0,0,157,158,1,0,0,0,158,
  	159,5,5,0,0,159,160,5,4,0,0,160,161,5,5,0,0,161,167,4,9,10,1,162,164,
  	5,19,0,0,163,162,1,0,0,0,163,164,1,0,0,0,164,165,1,0,0,0,165,167,5,5,
  	0,0,166,156,1,0,0,0,166,163,1,0,0,0,167,19,1,0,0,0,168,169,6,10,-1,0,
  	169,170,3,22,11,0,170,176,1,0,0,0,171,172,10,1,0,0,172,173,5,3,0,0,173,
  	175,3,22,11,0,174,171,1,0,0,0,175,178,1,0,0,0,176,174,1,0,0,0,176,177,
  	1,0,0,0,177,21,1,0,0,0,178,176,1,0,0,0,179,180,5,2,0,0,180,181,5,25,0,
  	0,181,182,5,2,0,0,182,183,5,8,0,0,183,184,5,5,0,0,184,185,4,11,12,1,185,
  	23,1,0,0,0,17,28,35,49,66,78,80,91,102,110,136,140,150,152,156,163,166,
  	176
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

ExtendedDiracParser::AcceptedContext* ExtendedDiracParser::ExtendedDiracContext::accepted() {
  return getRuleContext<ExtendedDiracParser::AcceptedContext>(0);
}

tree::TerminalNode* ExtendedDiracParser::ExtendedDiracContext::EOF() {
  return getToken(ExtendedDiracParser::EOF, 0);
}

tree::TerminalNode* ExtendedDiracParser::ExtendedDiracContext::WHERE() {
  return getToken(ExtendedDiracParser::WHERE, 0);
}

tree::TerminalNode* ExtendedDiracParser::ExtendedDiracContext::NEWLINES() {
  return getToken(ExtendedDiracParser::NEWLINES, 0);
}

ExtendedDiracParser::MuloperatorsContext* ExtendedDiracParser::ExtendedDiracContext::muloperators() {
  return getRuleContext<ExtendedDiracParser::MuloperatorsContext>(0);
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
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(24);
    accepted();
    setState(28);
    _errHandler->sync(this);

    _la = _input->LA(1);
    if (_la == ExtendedDiracParser::WHERE) {
      setState(25);
      match(ExtendedDiracParser::WHERE);
      setState(26);
      match(ExtendedDiracParser::NEWLINES);
      setState(27);
      muloperators();
    }
    setState(30);
    match(ExtendedDiracParser::EOF);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- MuloperatorsContext ------------------------------------------------------------------

ExtendedDiracParser::MuloperatorsContext::MuloperatorsContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<ExtendedDiracParser::MuloperatorContext *> ExtendedDiracParser::MuloperatorsContext::muloperator() {
  return getRuleContexts<ExtendedDiracParser::MuloperatorContext>();
}

ExtendedDiracParser::MuloperatorContext* ExtendedDiracParser::MuloperatorsContext::muloperator(size_t i) {
  return getRuleContext<ExtendedDiracParser::MuloperatorContext>(i);
}


size_t ExtendedDiracParser::MuloperatorsContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleMuloperators;
}

void ExtendedDiracParser::MuloperatorsContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterMuloperators(this);
}

void ExtendedDiracParser::MuloperatorsContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitMuloperators(this);
}


std::any ExtendedDiracParser::MuloperatorsContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitMuloperators(this);
  else
    return visitor->visitChildren(this);
}

ExtendedDiracParser::MuloperatorsContext* ExtendedDiracParser::muloperators() {
  MuloperatorsContext *_localctx = _tracker.createInstance<MuloperatorsContext>(_ctx, getState());
  enterRule(_localctx, 2, ExtendedDiracParser::RuleMuloperators);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(33); 
    _errHandler->sync(this);
    _la = _input->LA(1);
    do {
      setState(32);
      muloperator();
      setState(35); 
      _errHandler->sync(this);
      _la = _input->LA(1);
    } while ((((_la & ~ 0x3fULL) == 0) &&
      ((1ULL << _la) & 36178144) != 0));
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- MuloperatorContext ------------------------------------------------------------------

ExtendedDiracParser::MuloperatorContext::MuloperatorContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<ExtendedDiracParser::ComplexContext *> ExtendedDiracParser::MuloperatorContext::complex() {
  return getRuleContexts<ExtendedDiracParser::ComplexContext>();
}

ExtendedDiracParser::ComplexContext* ExtendedDiracParser::MuloperatorContext::complex(size_t i) {
  return getRuleContext<ExtendedDiracParser::ComplexContext>(i);
}

tree::TerminalNode* ExtendedDiracParser::MuloperatorContext::PROD() {
  return getToken(ExtendedDiracParser::PROD, 0);
}

tree::TerminalNode* ExtendedDiracParser::MuloperatorContext::EQ() {
  return getToken(ExtendedDiracParser::EQ, 0);
}

tree::TerminalNode* ExtendedDiracParser::MuloperatorContext::NEWLINES() {
  return getToken(ExtendedDiracParser::NEWLINES, 0);
}

tree::TerminalNode* ExtendedDiracParser::MuloperatorContext::EOF() {
  return getToken(ExtendedDiracParser::EOF, 0);
}


size_t ExtendedDiracParser::MuloperatorContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleMuloperator;
}

void ExtendedDiracParser::MuloperatorContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterMuloperator(this);
}

void ExtendedDiracParser::MuloperatorContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitMuloperator(this);
}


std::any ExtendedDiracParser::MuloperatorContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitMuloperator(this);
  else
    return visitor->visitChildren(this);
}

ExtendedDiracParser::MuloperatorContext* ExtendedDiracParser::muloperator() {
  MuloperatorContext *_localctx = _tracker.createInstance<MuloperatorContext>(_ctx, getState());
  enterRule(_localctx, 4, ExtendedDiracParser::RuleMuloperator);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(37);
    complex(0);
    setState(38);
    match(ExtendedDiracParser::PROD);
    setState(39);
    complex(0);
    setState(40);
    match(ExtendedDiracParser::EQ);
    setState(41);
    complex(0);
    setState(42);
    _la = _input->LA(1);
    if (!(_la == ExtendedDiracParser::EOF

    || _la == ExtendedDiracParser::NEWLINES)) {
    _errHandler->recoverInline(this);
    }
    else {
      _errHandler->reportMatch(this);
      consume();
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- AcceptedContext ------------------------------------------------------------------

ExtendedDiracParser::AcceptedContext::AcceptedContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<ExtendedDiracParser::SetContext *> ExtendedDiracParser::AcceptedContext::set() {
  return getRuleContexts<ExtendedDiracParser::SetContext>();
}

ExtendedDiracParser::SetContext* ExtendedDiracParser::AcceptedContext::set(size_t i) {
  return getRuleContext<ExtendedDiracParser::SetContext>(i);
}

tree::TerminalNode* ExtendedDiracParser::AcceptedContext::SETMINUS() {
  return getToken(ExtendedDiracParser::SETMINUS, 0);
}


size_t ExtendedDiracParser::AcceptedContext::getRuleIndex() const {
  return ExtendedDiracParser::RuleAccepted;
}

void ExtendedDiracParser::AcceptedContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterAccepted(this);
}

void ExtendedDiracParser::AcceptedContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<ExtendedDiracParserListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitAccepted(this);
}


std::any ExtendedDiracParser::AcceptedContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<ExtendedDiracParserVisitor*>(visitor))
    return parserVisitor->visitAccepted(this);
  else
    return visitor->visitChildren(this);
}

ExtendedDiracParser::AcceptedContext* ExtendedDiracParser::accepted() {
  AcceptedContext *_localctx = _tracker.createInstance<AcceptedContext>(_ctx, getState());
  enterRule(_localctx, 6, ExtendedDiracParser::RuleAccepted);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(49);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 2, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(44);
      set(0);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(45);
      set(0);
      setState(46);
      match(ExtendedDiracParser::SETMINUS);
      setState(47);
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
  size_t startState = 8;
  enterRecursionRule(_localctx, 8, ExtendedDiracParser::RuleSet, precedence);

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
    setState(66);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 3, _ctx)) {
    case 1: {
      setState(52);
      match(ExtendedDiracParser::LEFT_BRACKET);
      setState(53);
      set(0);
      setState(54);
      match(ExtendedDiracParser::RIGHT_BRACKET);
      break;
    }

    case 2: {
      setState(56);
      match(ExtendedDiracParser::LEFT_CURLY_BRACKET);
      setState(57);
      diracs(0);
      setState(58);
      match(ExtendedDiracParser::RIGHT_CURLY_BRACKET);
      break;
    }

    case 3: {
      setState(60);
      match(ExtendedDiracParser::LEFT_CURLY_BRACKET);
      setState(61);
      dirac(0);
      setState(62);
      match(ExtendedDiracParser::BAR);
      setState(63);
      ijklens(0);
      setState(64);
      match(ExtendedDiracParser::RIGHT_CURLY_BRACKET);
      break;
    }

    default:
      break;
    }
    _ctx->stop = _input->LT(-1);
    setState(80);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 5, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        setState(78);
        _errHandler->sync(this);
        switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 4, _ctx)) {
        case 1: {
          _localctx = _tracker.createInstance<SetContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleSet);
          setState(68);

          if (!(precpred(_ctx, 2))) throw FailedPredicateException(this, "precpred(_ctx, 2)");
          setState(69);
          antlrcpp::downCast<SetContext *>(_localctx)->op = match(ExtendedDiracParser::PROD);
          setState(70);
          set(3);
          break;
        }

        case 2: {
          _localctx = _tracker.createInstance<SetContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleSet);
          setState(71);

          if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
          setState(72);
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
          setState(73);
          set(2);
          break;
        }

        case 3: {
          _localctx = _tracker.createInstance<SetContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleSet);
          setState(74);

          if (!(precpred(_ctx, 6))) throw FailedPredicateException(this, "precpred(_ctx, 6)");
          setState(75);
          match(ExtendedDiracParser::POWER);
          setState(76);
          antlrcpp::downCast<SetContext *>(_localctx)->n = match(ExtendedDiracParser::DIGITS);
          setState(77);

          if (!(isNonZero((antlrcpp::downCast<SetContext *>(_localctx)->n != nullptr ? antlrcpp::downCast<SetContext *>(_localctx)->n->getText() : "")))) throw FailedPredicateException(this, "isNonZero($n.text)");
          break;
        }

        default:
          break;
        } 
      }
      setState(82);
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
  size_t startState = 10;
  enterRecursionRule(_localctx, 10, ExtendedDiracParser::RuleDiracs, precedence);

    

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
    setState(84);
    dirac(0);
    _ctx->stop = _input->LT(-1);
    setState(91);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 6, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<DiracsContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleDiracs);
        setState(86);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(87);
        match(ExtendedDiracParser::COMMA);
        setState(88);
        dirac(0); 
      }
      setState(93);
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
  size_t startState = 12;
  enterRecursionRule(_localctx, 12, ExtendedDiracParser::RuleDirac, precedence);

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
    setState(95);
    cket();
    _ctx->stop = _input->LT(-1);
    setState(102);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 7, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<DiracContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleDirac);
        setState(97);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(98);
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
        setState(99);
        cket(); 
      }
      setState(104);
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
  enterRule(_localctx, 14, ExtendedDiracParser::RuleCket);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(110);
    _errHandler->sync(this);

    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 8, _ctx)) {
    case 1: {
      setState(105);
      complex(0);
      break;
    }

    case 2: {
      setState(106);
      complex(0);
      setState(107);
      antlrcpp::downCast<CketContext *>(_localctx)->op = match(ExtendedDiracParser::MUL);
      break;
    }

    case 3: {
      setState(109);
      match(ExtendedDiracParser::SUB);
      break;
    }

    default:
      break;
    }
    setState(112);
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
  size_t startState = 16;
  enterRecursionRule(_localctx, 16, ExtendedDiracParser::RuleComplex, precedence);

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
    setState(136);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case ExtendedDiracParser::LEFT_BRACKET: {
        setState(116);
        match(ExtendedDiracParser::LEFT_BRACKET);
        setState(117);
        complex(0);
        setState(118);
        match(ExtendedDiracParser::RIGHT_BRACKET);
        break;
      }

      case ExtendedDiracParser::SUB: {
        setState(120);
        match(ExtendedDiracParser::SUB);
        setState(121);
        complex(6);
        break;
      }

      case ExtendedDiracParser::EI2PI: {
        setState(122);
        match(ExtendedDiracParser::EI2PI);
        setState(123);
        match(ExtendedDiracParser::LEFT_BRACKET);
        setState(124);
        angle();
        setState(125);
        match(ExtendedDiracParser::RIGHT_BRACKET);
        break;
      }

      case ExtendedDiracParser::EIPI: {
        setState(127);
        match(ExtendedDiracParser::EIPI);
        setState(128);
        match(ExtendedDiracParser::LEFT_BRACKET);
        setState(129);
        angle();
        setState(130);
        match(ExtendedDiracParser::RIGHT_BRACKET);
        break;
      }

      case ExtendedDiracParser::DIGITS: {
        setState(132);
        match(ExtendedDiracParser::DIGITS);
        break;
      }

      case ExtendedDiracParser::SQRT2: {
        setState(133);
        match(ExtendedDiracParser::SQRT2);
        break;
      }

      case ExtendedDiracParser::NAME: {
        setState(134);
        antlrcpp::downCast<ComplexContext *>(_localctx)->var = match(ExtendedDiracParser::NAME);
         if (!predefinedVars.contains((antlrcpp::downCast<ComplexContext *>(_localctx)->var != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->var->getText() : ""))) isSymbolicAutomaton = true; 
        break;
      }

    default:
      throw NoViableAltException(this);
    }
    _ctx->stop = _input->LT(-1);
    setState(152);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 12, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        setState(150);
        _errHandler->sync(this);
        switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 11, _ctx)) {
        case 1: {
          _localctx = _tracker.createInstance<ComplexContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleComplex);
          setState(138);

          if (!(precpred(_ctx, 9))) throw FailedPredicateException(this, "precpred(_ctx, 9)");
          setState(140);
          _errHandler->sync(this);

          _la = _input->LA(1);
          if (_la == ExtendedDiracParser::DIV

          || _la == ExtendedDiracParser::MUL) {
            setState(139);
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
          setState(142);
          complex(10);
          break;
        }

        case 2: {
          _localctx = _tracker.createInstance<ComplexContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleComplex);
          setState(143);

          if (!(precpred(_ctx, 8))) throw FailedPredicateException(this, "precpred(_ctx, 8)");
          setState(144);
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
          setState(145);
          complex(9);
          break;
        }

        case 3: {
          _localctx = _tracker.createInstance<ComplexContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleComplex);
          setState(146);

          if (!(precpred(_ctx, 10))) throw FailedPredicateException(this, "precpred(_ctx, 10)");
          setState(147);
          match(ExtendedDiracParser::POWER);
          setState(148);
          antlrcpp::downCast<ComplexContext *>(_localctx)->n = match(ExtendedDiracParser::DIGITS);
          setState(149);

          if (!(isNonZero((antlrcpp::downCast<ComplexContext *>(_localctx)->n != nullptr ? antlrcpp::downCast<ComplexContext *>(_localctx)->n->getText() : "")))) throw FailedPredicateException(this, "isNonZero($n.text)");
          break;
        }

        default:
          break;
        } 
      }
      setState(154);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 12, _ctx);
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
  enterRule(_localctx, 18, ExtendedDiracParser::RuleAngle);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(166);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 15, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(156);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == ExtendedDiracParser::SUB) {
        setState(155);
        match(ExtendedDiracParser::SUB);
      }
      setState(158);
      antlrcpp::downCast<AngleContext *>(_localctx)->x = match(ExtendedDiracParser::DIGITS);
      setState(159);
      match(ExtendedDiracParser::DIV);
      setState(160);
      antlrcpp::downCast<AngleContext *>(_localctx)->y = match(ExtendedDiracParser::DIGITS);
      setState(161);

      if (!(isNonZero((antlrcpp::downCast<AngleContext *>(_localctx)->y != nullptr ? antlrcpp::downCast<AngleContext *>(_localctx)->y->getText() : "")))) throw FailedPredicateException(this, "isNonZero($y.text)");
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(163);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == ExtendedDiracParser::SUB) {
        setState(162);
        match(ExtendedDiracParser::SUB);
      }
      setState(165);
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
  size_t startState = 20;
  enterRecursionRule(_localctx, 20, ExtendedDiracParser::RuleIjklens, precedence);

    

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
    setState(169);
    ijklen();
    _ctx->stop = _input->LT(-1);
    setState(176);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 16, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<IjklensContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleIjklens);
        setState(171);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(172);
        match(ExtendedDiracParser::COMMA);
        setState(173);
        ijklen(); 
      }
      setState(178);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 16, _ctx);
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
  enterRule(_localctx, 22, ExtendedDiracParser::RuleIjklen);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(179);
    match(ExtendedDiracParser::BAR);
    setState(180);
    antlrcpp::downCast<IjklenContext *>(_localctx)->var = match(ExtendedDiracParser::NAME);
    setState(181);
    match(ExtendedDiracParser::BAR);
    setState(182);
    match(ExtendedDiracParser::EQ);
    setState(183);
    antlrcpp::downCast<IjklenContext *>(_localctx)->len = match(ExtendedDiracParser::DIGITS);
    setState(184);

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
    case 4: return setSempred(antlrcpp::downCast<SetContext *>(context), predicateIndex);
    case 5: return diracsSempred(antlrcpp::downCast<DiracsContext *>(context), predicateIndex);
    case 6: return diracSempred(antlrcpp::downCast<DiracContext *>(context), predicateIndex);
    case 8: return complexSempred(antlrcpp::downCast<ComplexContext *>(context), predicateIndex);
    case 9: return angleSempred(antlrcpp::downCast<AngleContext *>(context), predicateIndex);
    case 10: return ijklensSempred(antlrcpp::downCast<IjklensContext *>(context), predicateIndex);
    case 11: return ijklenSempred(antlrcpp::downCast<IjklenContext *>(context), predicateIndex);

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
