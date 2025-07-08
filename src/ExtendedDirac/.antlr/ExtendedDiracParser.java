// Generated from /home/alan23273850/AutoQ/src/ExtendedDirac/ExtendedDiracParser.g4 by ANTLR 4.13.1
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast", "CheckReturnValue"})
public class ExtendedDiracParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.13.1", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		ADD=1, BAR=2, COMMA=3, COLON=4, EQ=5, LEFT_BRACE=6, NE=7, NEWLINES=8, 
		OR=9, POWER=10, PRIME=11, PROD=12, RIGHT_ANGLE_BRACKET=13, RIGHT_BRACE=14, 
		SEMICOLON=15, SETMINUS=16, STR=17, SUM=18, UNION=19, WS=20;
	public static final int
		RULE_expr = 0, RULE_tset = 1, RULE_set = 2, RULE_diracs = 3, RULE_dirac = 4, 
		RULE_term = 5, RULE_varcons = 6, RULE_varcon = 7, RULE_ineq = 8;
	private static String[] makeRuleNames() {
		return new String[] {
			"expr", "tset", "set", "diracs", "dirac", "term", "varcons", "varcon", 
			"ineq"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'+'", "'|'", "','", "':'", "'='", "'{'", "'\\u2260'", null, "'\\u2228'", 
			"'^'", "'''", "'\\u2297'", null, "'}'", "';'", "'\\'", null, null, "'\\u222A'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "ADD", "BAR", "COMMA", "COLON", "EQ", "LEFT_BRACE", "NE", "NEWLINES", 
			"OR", "POWER", "PRIME", "PROD", "RIGHT_ANGLE_BRACKET", "RIGHT_BRACE", 
			"SEMICOLON", "SETMINUS", "STR", "SUM", "UNION", "WS"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "ExtendedDiracParser.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }


	    bool isSymbolicAutomaton = false;
	    std::set<std::string> predefinedVars;

	    bool isNonZero(const std::string& text) {
	        return std::stoi(text) != 0;
	    }
	    bool isALowercaseLetter(const std::string& text) {
	        return text.length() == 1 && 'a' <= text.at(0) && text.at(0) <= 'z';
	    }
	    bool isAConstantBinaryString(const std::string& text) {
	        return std::all_of(text.begin(), text.end(), [](char c) { return c == '0' || c == '1'; });
	    }

	public ExtendedDiracParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ExprContext extends ParserRuleContext {
		public Token op;
		public List<TsetContext> tset() {
			return getRuleContexts(TsetContext.class);
		}
		public TsetContext tset(int i) {
			return getRuleContext(TsetContext.class,i);
		}
		public TerminalNode SETMINUS() { return getToken(ExtendedDiracParser.SETMINUS, 0); }
		public ExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expr; }
	}

	public final ExprContext expr() throws RecognitionException {
		ExprContext _localctx = new ExprContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_expr);
		try {
			setState(23);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,0,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(18);
				tset(0);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(19);
				tset(0);
				setState(20);
				((ExprContext)_localctx).op = match(SETMINUS);
				setState(21);
				tset(0);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class TsetContext extends ParserRuleContext {
		public Token op;
		public Token N;
		public List<SetContext> set() {
			return getRuleContexts(SetContext.class);
		}
		public SetContext set(int i) {
			return getRuleContext(SetContext.class,i);
		}
		public TerminalNode POWER() { return getToken(ExtendedDiracParser.POWER, 0); }
		public TerminalNode STR() { return getToken(ExtendedDiracParser.STR, 0); }
		public List<TerminalNode> SEMICOLON() { return getTokens(ExtendedDiracParser.SEMICOLON); }
		public TerminalNode SEMICOLON(int i) {
			return getToken(ExtendedDiracParser.SEMICOLON, i);
		}
		public List<TsetContext> tset() {
			return getRuleContexts(TsetContext.class);
		}
		public TsetContext tset(int i) {
			return getRuleContext(TsetContext.class,i);
		}
		public TerminalNode PROD() { return getToken(ExtendedDiracParser.PROD, 0); }
		public TsetContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_tset; }
	}

	public final TsetContext tset() throws RecognitionException {
		return tset(0);
	}

	private TsetContext tset(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		TsetContext _localctx = new TsetContext(_ctx, _parentState);
		TsetContext _prevctx = _localctx;
		int _startState = 2;
		enterRecursionRule(_localctx, 2, RULE_tset, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(50);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,1,_ctx) ) {
			case 1:
				{
				setState(26);
				set(0);
				}
				break;
			case 2:
				{
				setState(27);
				set(0);
				setState(28);
				((TsetContext)_localctx).op = match(POWER);
				setState(29);
				((TsetContext)_localctx).N = match(STR);
				setState(30);
				if (!(isNonZero((((TsetContext)_localctx).N!=null?((TsetContext)_localctx).N.getText():null)))) throw new FailedPredicateException(this, "isNonZero($N.text)");
				}
				break;
			case 3:
				{
				setState(32);
				set(0);
				setState(33);
				((TsetContext)_localctx).op = match(SEMICOLON);
				setState(34);
				set(0);
				}
				break;
			case 4:
				{
				setState(36);
				set(0);
				setState(37);
				((TsetContext)_localctx).op = match(SEMICOLON);
				setState(38);
				set(0);
				setState(39);
				match(SEMICOLON);
				setState(40);
				set(0);
				}
				break;
			case 5:
				{
				setState(42);
				set(0);
				setState(43);
				((TsetContext)_localctx).op = match(SEMICOLON);
				setState(44);
				set(0);
				setState(45);
				match(SEMICOLON);
				setState(46);
				set(0);
				setState(47);
				match(SEMICOLON);
				setState(48);
				set(0);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(57);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,2,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new TsetContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_tset);
					setState(52);
					if (!(precpred(_ctx, 4))) throw new FailedPredicateException(this, "precpred(_ctx, 4)");
					setState(53);
					((TsetContext)_localctx).op = match(PROD);
					setState(54);
					tset(5);
					}
					} 
				}
				setState(59);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,2,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class SetContext extends ParserRuleContext {
		public Token op;
		public TerminalNode LEFT_BRACE() { return getToken(ExtendedDiracParser.LEFT_BRACE, 0); }
		public DiracsContext diracs() {
			return getRuleContext(DiracsContext.class,0);
		}
		public TerminalNode RIGHT_BRACE() { return getToken(ExtendedDiracParser.RIGHT_BRACE, 0); }
		public TerminalNode COLON() { return getToken(ExtendedDiracParser.COLON, 0); }
		public VarconsContext varcons() {
			return getRuleContext(VarconsContext.class,0);
		}
		public List<SetContext> set() {
			return getRuleContexts(SetContext.class);
		}
		public SetContext set(int i) {
			return getRuleContext(SetContext.class,i);
		}
		public TerminalNode UNION() { return getToken(ExtendedDiracParser.UNION, 0); }
		public SetContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_set; }
	}

	public final SetContext set() throws RecognitionException {
		return set(0);
	}

	private SetContext set(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		SetContext _localctx = new SetContext(_ctx, _parentState);
		SetContext _prevctx = _localctx;
		int _startState = 4;
		enterRecursionRule(_localctx, 4, RULE_set, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(71);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,3,_ctx) ) {
			case 1:
				{
				setState(61);
				match(LEFT_BRACE);
				setState(62);
				diracs(0);
				setState(63);
				match(RIGHT_BRACE);
				}
				break;
			case 2:
				{
				setState(65);
				match(LEFT_BRACE);
				setState(66);
				diracs(0);
				setState(67);
				match(COLON);
				setState(68);
				varcons(0);
				setState(69);
				match(RIGHT_BRACE);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(78);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,4,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new SetContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_set);
					setState(73);
					if (!(precpred(_ctx, 3))) throw new FailedPredicateException(this, "precpred(_ctx, 3)");
					setState(74);
					((SetContext)_localctx).op = match(UNION);
					setState(75);
					set(4);
					}
					} 
				}
				setState(80);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,4,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class DiracsContext extends ParserRuleContext {
		public DiracContext dirac() {
			return getRuleContext(DiracContext.class,0);
		}
		public DiracsContext diracs() {
			return getRuleContext(DiracsContext.class,0);
		}
		public TerminalNode COMMA() { return getToken(ExtendedDiracParser.COMMA, 0); }
		public DiracsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_diracs; }
	}

	public final DiracsContext diracs() throws RecognitionException {
		return diracs(0);
	}

	private DiracsContext diracs(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		DiracsContext _localctx = new DiracsContext(_ctx, _parentState);
		DiracsContext _prevctx = _localctx;
		int _startState = 6;
		enterRecursionRule(_localctx, 6, RULE_diracs, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(82);
			dirac(0);
			}
			_ctx.stop = _input.LT(-1);
			setState(89);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,5,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new DiracsContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_diracs);
					setState(84);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(85);
					match(COMMA);
					setState(86);
					dirac(0);
					}
					} 
				}
				setState(91);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,5,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class DiracContext extends ParserRuleContext {
		public Token op;
		public TermContext term() {
			return getRuleContext(TermContext.class,0);
		}
		public DiracContext dirac() {
			return getRuleContext(DiracContext.class,0);
		}
		public TerminalNode ADD() { return getToken(ExtendedDiracParser.ADD, 0); }
		public DiracContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_dirac; }
	}

	public final DiracContext dirac() throws RecognitionException {
		return dirac(0);
	}

	private DiracContext dirac(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		DiracContext _localctx = new DiracContext(_ctx, _parentState);
		DiracContext _prevctx = _localctx;
		int _startState = 8;
		enterRecursionRule(_localctx, 8, RULE_dirac, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(93);
			term();
			}
			_ctx.stop = _input.LT(-1);
			setState(100);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,6,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new DiracContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_dirac);
					setState(95);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(96);
					((DiracContext)_localctx).op = match(ADD);
					setState(97);
					term();
					}
					} 
				}
				setState(102);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,6,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class TermContext extends ParserRuleContext {
		public Token C;
		public Token VStr;
		public TerminalNode BAR() { return getToken(ExtendedDiracParser.BAR, 0); }
		public TerminalNode RIGHT_ANGLE_BRACKET() { return getToken(ExtendedDiracParser.RIGHT_ANGLE_BRACKET, 0); }
		public List<TerminalNode> STR() { return getTokens(ExtendedDiracParser.STR); }
		public TerminalNode STR(int i) {
			return getToken(ExtendedDiracParser.STR, i);
		}
		public TerminalNode SUM() { return getToken(ExtendedDiracParser.SUM, 0); }
		public VarconsContext varcons() {
			return getRuleContext(VarconsContext.class,0);
		}
		public TermContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_term; }
	}

	public final TermContext term() throws RecognitionException {
		TermContext _localctx = new TermContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_term);
		try {
			setState(114);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,7,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(103);
				((TermContext)_localctx).C = match(STR);
				setState(104);
				match(BAR);
				setState(105);
				((TermContext)_localctx).VStr = match(STR);
				setState(106);
				match(RIGHT_ANGLE_BRACKET);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(107);
				((TermContext)_localctx).C = match(STR);
				setState(108);
				match(SUM);
				setState(109);
				varcons(0);
				setState(110);
				match(BAR);
				setState(111);
				((TermContext)_localctx).VStr = match(STR);
				setState(112);
				match(RIGHT_ANGLE_BRACKET);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class VarconsContext extends ParserRuleContext {
		public VarconContext varcon() {
			return getRuleContext(VarconContext.class,0);
		}
		public VarconsContext varcons() {
			return getRuleContext(VarconsContext.class,0);
		}
		public TerminalNode COMMA() { return getToken(ExtendedDiracParser.COMMA, 0); }
		public VarconsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_varcons; }
	}

	public final VarconsContext varcons() throws RecognitionException {
		return varcons(0);
	}

	private VarconsContext varcons(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		VarconsContext _localctx = new VarconsContext(_ctx, _parentState);
		VarconsContext _prevctx = _localctx;
		int _startState = 12;
		enterRecursionRule(_localctx, 12, RULE_varcons, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(117);
			varcon();
			}
			_ctx.stop = _input.LT(-1);
			setState(124);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,8,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new VarconsContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_varcons);
					setState(119);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(120);
					match(COMMA);
					setState(121);
					varcon();
					}
					} 
				}
				setState(126);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,8,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class VarconContext extends ParserRuleContext {
		public Token V;
		public Token N;
		public Token CStr;
		public List<TerminalNode> BAR() { return getTokens(ExtendedDiracParser.BAR); }
		public TerminalNode BAR(int i) {
			return getToken(ExtendedDiracParser.BAR, i);
		}
		public TerminalNode EQ() { return getToken(ExtendedDiracParser.EQ, 0); }
		public List<TerminalNode> STR() { return getTokens(ExtendedDiracParser.STR); }
		public TerminalNode STR(int i) {
			return getToken(ExtendedDiracParser.STR, i);
		}
		public IneqContext ineq() {
			return getRuleContext(IneqContext.class,0);
		}
		public VarconContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_varcon; }
	}

	public final VarconContext varcon() throws RecognitionException {
		VarconContext _localctx = new VarconContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_varcon);
		try {
			setState(138);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,9,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(127);
				match(BAR);
				setState(128);
				((VarconContext)_localctx).V = match(STR);
				setState(129);
				match(BAR);
				setState(130);
				match(EQ);
				setState(131);
				((VarconContext)_localctx).N = match(STR);
				setState(132);
				if (!(isALowercaseLetter((((VarconContext)_localctx).V!=null?((VarconContext)_localctx).V.getText():null)) && isNonZero((((VarconContext)_localctx).N!=null?((VarconContext)_localctx).N.getText():null)))) throw new FailedPredicateException(this, "isALowercaseLetter($V.text) && isNonZero($N.text)");
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(133);
				((VarconContext)_localctx).V = match(STR);
				setState(134);
				match(EQ);
				setState(135);
				((VarconContext)_localctx).CStr = match(STR);
				setState(136);
				if (!(isALowercaseLetter((((VarconContext)_localctx).V!=null?((VarconContext)_localctx).V.getText():null)) && isAConstantBinaryString((((VarconContext)_localctx).CStr!=null?((VarconContext)_localctx).CStr.getText():null)))) throw new FailedPredicateException(this, "isALowercaseLetter($V.text) && isAConstantBinaryString($CStr.text)");
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(137);
				ineq();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class IneqContext extends ParserRuleContext {
		public Token L;
		public Token R;
		public TerminalNode NE() { return getToken(ExtendedDiracParser.NE, 0); }
		public List<TerminalNode> STR() { return getTokens(ExtendedDiracParser.STR); }
		public TerminalNode STR(int i) {
			return getToken(ExtendedDiracParser.STR, i);
		}
		public IneqContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_ineq; }
	}

	public final IneqContext ineq() throws RecognitionException {
		IneqContext _localctx = new IneqContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_ineq);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(140);
			((IneqContext)_localctx).L = match(STR);
			setState(141);
			match(NE);
			setState(142);
			((IneqContext)_localctx).R = match(STR);
			setState(143);
			if (!(isALowercaseLetter((((IneqContext)_localctx).L!=null?((IneqContext)_localctx).L.getText():null)) && (isALowercaseLetter((((IneqContext)_localctx).R!=null?((IneqContext)_localctx).R.getText():null)) || isAConstantBinaryString((((IneqContext)_localctx).R!=null?((IneqContext)_localctx).R.getText():null))))) throw new FailedPredicateException(this, "isALowercaseLetter($L.text) && (isALowercaseLetter($R.text) || isAConstantBinaryString($R.text))");
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public boolean sempred(RuleContext _localctx, int ruleIndex, int predIndex) {
		switch (ruleIndex) {
		case 1:
			return tset_sempred((TsetContext)_localctx, predIndex);
		case 2:
			return set_sempred((SetContext)_localctx, predIndex);
		case 3:
			return diracs_sempred((DiracsContext)_localctx, predIndex);
		case 4:
			return dirac_sempred((DiracContext)_localctx, predIndex);
		case 6:
			return varcons_sempred((VarconsContext)_localctx, predIndex);
		case 7:
			return varcon_sempred((VarconContext)_localctx, predIndex);
		case 8:
			return ineq_sempred((IneqContext)_localctx, predIndex);
		}
		return true;
	}
	private boolean tset_sempred(TsetContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return isNonZero((((TsetContext)_localctx).N!=null?((TsetContext)_localctx).N.getText():null));
		case 1:
			return precpred(_ctx, 4);
		}
		return true;
	}
	private boolean set_sempred(SetContext _localctx, int predIndex) {
		switch (predIndex) {
		case 2:
			return precpred(_ctx, 3);
		}
		return true;
	}
	private boolean diracs_sempred(DiracsContext _localctx, int predIndex) {
		switch (predIndex) {
		case 3:
			return precpred(_ctx, 1);
		}
		return true;
	}
	private boolean dirac_sempred(DiracContext _localctx, int predIndex) {
		switch (predIndex) {
		case 4:
			return precpred(_ctx, 1);
		}
		return true;
	}
	private boolean varcons_sempred(VarconsContext _localctx, int predIndex) {
		switch (predIndex) {
		case 5:
			return precpred(_ctx, 1);
		}
		return true;
	}
	private boolean varcon_sempred(VarconContext _localctx, int predIndex) {
		switch (predIndex) {
		case 6:
			return isALowercaseLetter((((VarconContext)_localctx).V!=null?((VarconContext)_localctx).V.getText():null)) && isNonZero((((VarconContext)_localctx).N!=null?((VarconContext)_localctx).N.getText():null));
		case 7:
			return isALowercaseLetter((((VarconContext)_localctx).V!=null?((VarconContext)_localctx).V.getText():null)) && isAConstantBinaryString((((VarconContext)_localctx).CStr!=null?((VarconContext)_localctx).CStr.getText():null));
		}
		return true;
	}
	private boolean ineq_sempred(IneqContext _localctx, int predIndex) {
		switch (predIndex) {
		case 8:
			return isALowercaseLetter((((IneqContext)_localctx).L!=null?((IneqContext)_localctx).L.getText():null)) && (isALowercaseLetter((((IneqContext)_localctx).R!=null?((IneqContext)_localctx).R.getText():null)) || isAConstantBinaryString((((IneqContext)_localctx).R!=null?((IneqContext)_localctx).R.getText():null)));
		}
		return true;
	}

	public static final String _serializedATN =
		"\u0004\u0001\u0014\u0092\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001"+
		"\u0002\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004"+
		"\u0002\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007"+
		"\u0002\b\u0007\b\u0001\u0000\u0001\u0000\u0001\u0000\u0001\u0000\u0001"+
		"\u0000\u0003\u0000\u0018\b\u0000\u0001\u0001\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0003\u00013\b\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0005\u00018\b\u0001\n\u0001\f\u0001;\t"+
		"\u0001\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001"+
		"\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0003"+
		"\u0002H\b\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0005\u0002M\b\u0002"+
		"\n\u0002\f\u0002P\t\u0002\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003"+
		"\u0001\u0003\u0001\u0003\u0005\u0003X\b\u0003\n\u0003\f\u0003[\t\u0003"+
		"\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004"+
		"\u0005\u0004c\b\u0004\n\u0004\f\u0004f\t\u0004\u0001\u0005\u0001\u0005"+
		"\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005"+
		"\u0001\u0005\u0001\u0005\u0001\u0005\u0003\u0005s\b\u0005\u0001\u0006"+
		"\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0005\u0006"+
		"{\b\u0006\n\u0006\f\u0006~\t\u0006\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0003\u0007\u008b\b\u0007\u0001\b\u0001\b\u0001"+
		"\b\u0001\b\u0001\b\u0001\b\u0000\u0005\u0002\u0004\u0006\b\f\t\u0000\u0002"+
		"\u0004\u0006\b\n\f\u000e\u0010\u0000\u0000\u0096\u0000\u0017\u0001\u0000"+
		"\u0000\u0000\u00022\u0001\u0000\u0000\u0000\u0004G\u0001\u0000\u0000\u0000"+
		"\u0006Q\u0001\u0000\u0000\u0000\b\\\u0001\u0000\u0000\u0000\nr\u0001\u0000"+
		"\u0000\u0000\ft\u0001\u0000\u0000\u0000\u000e\u008a\u0001\u0000\u0000"+
		"\u0000\u0010\u008c\u0001\u0000\u0000\u0000\u0012\u0018\u0003\u0002\u0001"+
		"\u0000\u0013\u0014\u0003\u0002\u0001\u0000\u0014\u0015\u0005\u0010\u0000"+
		"\u0000\u0015\u0016\u0003\u0002\u0001\u0000\u0016\u0018\u0001\u0000\u0000"+
		"\u0000\u0017\u0012\u0001\u0000\u0000\u0000\u0017\u0013\u0001\u0000\u0000"+
		"\u0000\u0018\u0001\u0001\u0000\u0000\u0000\u0019\u001a\u0006\u0001\uffff"+
		"\uffff\u0000\u001a3\u0003\u0004\u0002\u0000\u001b\u001c\u0003\u0004\u0002"+
		"\u0000\u001c\u001d\u0005\n\u0000\u0000\u001d\u001e\u0005\u0011\u0000\u0000"+
		"\u001e\u001f\u0004\u0001\u0000\u0001\u001f3\u0001\u0000\u0000\u0000 !"+
		"\u0003\u0004\u0002\u0000!\"\u0005\u000f\u0000\u0000\"#\u0003\u0004\u0002"+
		"\u0000#3\u0001\u0000\u0000\u0000$%\u0003\u0004\u0002\u0000%&\u0005\u000f"+
		"\u0000\u0000&\'\u0003\u0004\u0002\u0000\'(\u0005\u000f\u0000\u0000()\u0003"+
		"\u0004\u0002\u0000)3\u0001\u0000\u0000\u0000*+\u0003\u0004\u0002\u0000"+
		"+,\u0005\u000f\u0000\u0000,-\u0003\u0004\u0002\u0000-.\u0005\u000f\u0000"+
		"\u0000./\u0003\u0004\u0002\u0000/0\u0005\u000f\u0000\u000001\u0003\u0004"+
		"\u0002\u000013\u0001\u0000\u0000\u00002\u0019\u0001\u0000\u0000\u0000"+
		"2\u001b\u0001\u0000\u0000\u00002 \u0001\u0000\u0000\u00002$\u0001\u0000"+
		"\u0000\u00002*\u0001\u0000\u0000\u000039\u0001\u0000\u0000\u000045\n\u0004"+
		"\u0000\u000056\u0005\f\u0000\u000068\u0003\u0002\u0001\u000574\u0001\u0000"+
		"\u0000\u00008;\u0001\u0000\u0000\u000097\u0001\u0000\u0000\u00009:\u0001"+
		"\u0000\u0000\u0000:\u0003\u0001\u0000\u0000\u0000;9\u0001\u0000\u0000"+
		"\u0000<=\u0006\u0002\uffff\uffff\u0000=>\u0005\u0006\u0000\u0000>?\u0003"+
		"\u0006\u0003\u0000?@\u0005\u000e\u0000\u0000@H\u0001\u0000\u0000\u0000"+
		"AB\u0005\u0006\u0000\u0000BC\u0003\u0006\u0003\u0000CD\u0005\u0004\u0000"+
		"\u0000DE\u0003\f\u0006\u0000EF\u0005\u000e\u0000\u0000FH\u0001\u0000\u0000"+
		"\u0000G<\u0001\u0000\u0000\u0000GA\u0001\u0000\u0000\u0000HN\u0001\u0000"+
		"\u0000\u0000IJ\n\u0003\u0000\u0000JK\u0005\u0013\u0000\u0000KM\u0003\u0004"+
		"\u0002\u0004LI\u0001\u0000\u0000\u0000MP\u0001\u0000\u0000\u0000NL\u0001"+
		"\u0000\u0000\u0000NO\u0001\u0000\u0000\u0000O\u0005\u0001\u0000\u0000"+
		"\u0000PN\u0001\u0000\u0000\u0000QR\u0006\u0003\uffff\uffff\u0000RS\u0003"+
		"\b\u0004\u0000SY\u0001\u0000\u0000\u0000TU\n\u0001\u0000\u0000UV\u0005"+
		"\u0003\u0000\u0000VX\u0003\b\u0004\u0000WT\u0001\u0000\u0000\u0000X[\u0001"+
		"\u0000\u0000\u0000YW\u0001\u0000\u0000\u0000YZ\u0001\u0000\u0000\u0000"+
		"Z\u0007\u0001\u0000\u0000\u0000[Y\u0001\u0000\u0000\u0000\\]\u0006\u0004"+
		"\uffff\uffff\u0000]^\u0003\n\u0005\u0000^d\u0001\u0000\u0000\u0000_`\n"+
		"\u0001\u0000\u0000`a\u0005\u0001\u0000\u0000ac\u0003\n\u0005\u0000b_\u0001"+
		"\u0000\u0000\u0000cf\u0001\u0000\u0000\u0000db\u0001\u0000\u0000\u0000"+
		"de\u0001\u0000\u0000\u0000e\t\u0001\u0000\u0000\u0000fd\u0001\u0000\u0000"+
		"\u0000gh\u0005\u0011\u0000\u0000hi\u0005\u0002\u0000\u0000ij\u0005\u0011"+
		"\u0000\u0000js\u0005\r\u0000\u0000kl\u0005\u0011\u0000\u0000lm\u0005\u0012"+
		"\u0000\u0000mn\u0003\f\u0006\u0000no\u0005\u0002\u0000\u0000op\u0005\u0011"+
		"\u0000\u0000pq\u0005\r\u0000\u0000qs\u0001\u0000\u0000\u0000rg\u0001\u0000"+
		"\u0000\u0000rk\u0001\u0000\u0000\u0000s\u000b\u0001\u0000\u0000\u0000"+
		"tu\u0006\u0006\uffff\uffff\u0000uv\u0003\u000e\u0007\u0000v|\u0001\u0000"+
		"\u0000\u0000wx\n\u0001\u0000\u0000xy\u0005\u0003\u0000\u0000y{\u0003\u000e"+
		"\u0007\u0000zw\u0001\u0000\u0000\u0000{~\u0001\u0000\u0000\u0000|z\u0001"+
		"\u0000\u0000\u0000|}\u0001\u0000\u0000\u0000}\r\u0001\u0000\u0000\u0000"+
		"~|\u0001\u0000\u0000\u0000\u007f\u0080\u0005\u0002\u0000\u0000\u0080\u0081"+
		"\u0005\u0011\u0000\u0000\u0081\u0082\u0005\u0002\u0000\u0000\u0082\u0083"+
		"\u0005\u0005\u0000\u0000\u0083\u0084\u0005\u0011\u0000\u0000\u0084\u008b"+
		"\u0004\u0007\u0006\u0001\u0085\u0086\u0005\u0011\u0000\u0000\u0086\u0087"+
		"\u0005\u0005\u0000\u0000\u0087\u0088\u0005\u0011\u0000\u0000\u0088\u008b"+
		"\u0004\u0007\u0007\u0001\u0089\u008b\u0003\u0010\b\u0000\u008a\u007f\u0001"+
		"\u0000\u0000\u0000\u008a\u0085\u0001\u0000\u0000\u0000\u008a\u0089\u0001"+
		"\u0000\u0000\u0000\u008b\u000f\u0001\u0000\u0000\u0000\u008c\u008d\u0005"+
		"\u0011\u0000\u0000\u008d\u008e\u0005\u0007\u0000\u0000\u008e\u008f\u0005"+
		"\u0011\u0000\u0000\u008f\u0090\u0004\b\b\u0001\u0090\u0011\u0001\u0000"+
		"\u0000\u0000\n\u001729GNYdr|\u008a";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}