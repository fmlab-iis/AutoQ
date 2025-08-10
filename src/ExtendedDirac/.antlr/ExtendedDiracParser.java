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
		RULE_expr = 0, RULE_tset = 1, RULE_scset = 2, RULE_set = 3, RULE_diracs = 4, 
		RULE_dirac = 5, RULE_term = 6, RULE_varcons = 7, RULE_varcon = 8, RULE_ineq = 9;
	private static String[] makeRuleNames() {
		return new String[] {
			"expr", "tset", "scset", "set", "diracs", "dirac", "term", "varcons", 
			"varcon", "ineq"
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
			setState(25);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,0,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(20);
				tset(0);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(21);
				tset(0);
				setState(22);
				((ExprContext)_localctx).op = match(SETMINUS);
				setState(23);
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
		public ScsetContext scset() {
			return getRuleContext(ScsetContext.class,0);
		}
		public SetContext set() {
			return getRuleContext(SetContext.class,0);
		}
		public TerminalNode POWER() { return getToken(ExtendedDiracParser.POWER, 0); }
		public TerminalNode STR() { return getToken(ExtendedDiracParser.STR, 0); }
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
			setState(34);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,1,_ctx) ) {
			case 1:
				{
				setState(28);
				scset(0);
				}
				break;
			case 2:
				{
				setState(29);
				set(0);
				setState(30);
				((TsetContext)_localctx).op = match(POWER);
				setState(31);
				((TsetContext)_localctx).N = match(STR);
				setState(32);
				if (!(isNonZero((((TsetContext)_localctx).N!=null?((TsetContext)_localctx).N.getText():null)))) throw new FailedPredicateException(this, "isNonZero($N.text)");
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(41);
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
					setState(36);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(37);
					((TsetContext)_localctx).op = match(PROD);
					setState(38);
					tset(2);
					}
					} 
				}
				setState(43);
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
	public static class ScsetContext extends ParserRuleContext {
		public Token op;
		public SetContext set() {
			return getRuleContext(SetContext.class,0);
		}
		public ScsetContext scset() {
			return getRuleContext(ScsetContext.class,0);
		}
		public TerminalNode SEMICOLON() { return getToken(ExtendedDiracParser.SEMICOLON, 0); }
		public ScsetContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_scset; }
	}

	public final ScsetContext scset() throws RecognitionException {
		return scset(0);
	}

	private ScsetContext scset(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		ScsetContext _localctx = new ScsetContext(_ctx, _parentState);
		ScsetContext _prevctx = _localctx;
		int _startState = 4;
		enterRecursionRule(_localctx, 4, RULE_scset, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(45);
			set(0);
			}
			_ctx.stop = _input.LT(-1);
			setState(52);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,3,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new ScsetContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_scset);
					setState(47);
					if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
					setState(48);
					((ScsetContext)_localctx).op = match(SEMICOLON);
					setState(49);
					set(0);
					}
					} 
				}
				setState(54);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,3,_ctx);
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
		int _startState = 6;
		enterRecursionRule(_localctx, 6, RULE_set, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(66);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,4,_ctx) ) {
			case 1:
				{
				setState(56);
				match(LEFT_BRACE);
				setState(57);
				diracs(0);
				setState(58);
				match(RIGHT_BRACE);
				}
				break;
			case 2:
				{
				setState(60);
				match(LEFT_BRACE);
				setState(61);
				diracs(0);
				setState(62);
				match(COLON);
				setState(63);
				varcons(0);
				setState(64);
				match(RIGHT_BRACE);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(73);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,5,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new SetContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_set);
					setState(68);
					if (!(precpred(_ctx, 3))) throw new FailedPredicateException(this, "precpred(_ctx, 3)");
					setState(69);
					((SetContext)_localctx).op = match(UNION);
					setState(70);
					set(4);
					}
					} 
				}
				setState(75);
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
		int _startState = 8;
		enterRecursionRule(_localctx, 8, RULE_diracs, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(77);
			dirac(0);
			}
			_ctx.stop = _input.LT(-1);
			setState(84);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,6,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new DiracsContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_diracs);
					setState(79);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(80);
					match(COMMA);
					setState(81);
					dirac(0);
					}
					} 
				}
				setState(86);
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
		int _startState = 10;
		enterRecursionRule(_localctx, 10, RULE_dirac, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(88);
			term();
			}
			_ctx.stop = _input.LT(-1);
			setState(95);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,7,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new DiracContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_dirac);
					setState(90);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(91);
					((DiracContext)_localctx).op = match(ADD);
					setState(92);
					term();
					}
					} 
				}
				setState(97);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,7,_ctx);
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
		enterRule(_localctx, 12, RULE_term);
		try {
			setState(109);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,8,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(98);
				((TermContext)_localctx).C = match(STR);
				setState(99);
				match(BAR);
				setState(100);
				((TermContext)_localctx).VStr = match(STR);
				setState(101);
				match(RIGHT_ANGLE_BRACKET);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(102);
				((TermContext)_localctx).C = match(STR);
				setState(103);
				match(SUM);
				setState(104);
				varcons(0);
				setState(105);
				match(BAR);
				setState(106);
				((TermContext)_localctx).VStr = match(STR);
				setState(107);
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
		int _startState = 14;
		enterRecursionRule(_localctx, 14, RULE_varcons, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(112);
			varcon();
			}
			_ctx.stop = _input.LT(-1);
			setState(119);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,9,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new VarconsContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_varcons);
					setState(114);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(115);
					match(COMMA);
					setState(116);
					varcon();
					}
					} 
				}
				setState(121);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,9,_ctx);
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
		enterRule(_localctx, 16, RULE_varcon);
		try {
			setState(133);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,10,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(122);
				match(BAR);
				setState(123);
				((VarconContext)_localctx).V = match(STR);
				setState(124);
				match(BAR);
				setState(125);
				match(EQ);
				setState(126);
				((VarconContext)_localctx).N = match(STR);
				setState(127);
				if (!(isALowercaseLetter((((VarconContext)_localctx).V!=null?((VarconContext)_localctx).V.getText():null)) && isNonZero((((VarconContext)_localctx).N!=null?((VarconContext)_localctx).N.getText():null)))) throw new FailedPredicateException(this, "isALowercaseLetter($V.text) && isNonZero($N.text)");
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(128);
				((VarconContext)_localctx).V = match(STR);
				setState(129);
				match(EQ);
				setState(130);
				((VarconContext)_localctx).CStr = match(STR);
				setState(131);
				if (!(isALowercaseLetter((((VarconContext)_localctx).V!=null?((VarconContext)_localctx).V.getText():null)) && isAConstantBinaryString((((VarconContext)_localctx).CStr!=null?((VarconContext)_localctx).CStr.getText():null)))) throw new FailedPredicateException(this, "isALowercaseLetter($V.text) && isAConstantBinaryString($CStr.text)");
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(132);
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
		enterRule(_localctx, 18, RULE_ineq);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(135);
			((IneqContext)_localctx).L = match(STR);
			setState(136);
			match(NE);
			setState(137);
			((IneqContext)_localctx).R = match(STR);
			setState(138);
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
			return scset_sempred((ScsetContext)_localctx, predIndex);
		case 3:
			return set_sempred((SetContext)_localctx, predIndex);
		case 4:
			return diracs_sempred((DiracsContext)_localctx, predIndex);
		case 5:
			return dirac_sempred((DiracContext)_localctx, predIndex);
		case 7:
			return varcons_sempred((VarconsContext)_localctx, predIndex);
		case 8:
			return varcon_sempred((VarconContext)_localctx, predIndex);
		case 9:
			return ineq_sempred((IneqContext)_localctx, predIndex);
		}
		return true;
	}
	private boolean tset_sempred(TsetContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return isNonZero((((TsetContext)_localctx).N!=null?((TsetContext)_localctx).N.getText():null));
		case 1:
			return precpred(_ctx, 1);
		}
		return true;
	}
	private boolean scset_sempred(ScsetContext _localctx, int predIndex) {
		switch (predIndex) {
		case 2:
			return precpred(_ctx, 2);
		}
		return true;
	}
	private boolean set_sempred(SetContext _localctx, int predIndex) {
		switch (predIndex) {
		case 3:
			return precpred(_ctx, 3);
		}
		return true;
	}
	private boolean diracs_sempred(DiracsContext _localctx, int predIndex) {
		switch (predIndex) {
		case 4:
			return precpred(_ctx, 1);
		}
		return true;
	}
	private boolean dirac_sempred(DiracContext _localctx, int predIndex) {
		switch (predIndex) {
		case 5:
			return precpred(_ctx, 1);
		}
		return true;
	}
	private boolean varcons_sempred(VarconsContext _localctx, int predIndex) {
		switch (predIndex) {
		case 6:
			return precpred(_ctx, 1);
		}
		return true;
	}
	private boolean varcon_sempred(VarconContext _localctx, int predIndex) {
		switch (predIndex) {
		case 7:
			return isALowercaseLetter((((VarconContext)_localctx).V!=null?((VarconContext)_localctx).V.getText():null)) && isNonZero((((VarconContext)_localctx).N!=null?((VarconContext)_localctx).N.getText():null));
		case 8:
			return isALowercaseLetter((((VarconContext)_localctx).V!=null?((VarconContext)_localctx).V.getText():null)) && isAConstantBinaryString((((VarconContext)_localctx).CStr!=null?((VarconContext)_localctx).CStr.getText():null));
		}
		return true;
	}
	private boolean ineq_sempred(IneqContext _localctx, int predIndex) {
		switch (predIndex) {
		case 9:
			return isALowercaseLetter((((IneqContext)_localctx).L!=null?((IneqContext)_localctx).L.getText():null)) && (isALowercaseLetter((((IneqContext)_localctx).R!=null?((IneqContext)_localctx).R.getText():null)) || isAConstantBinaryString((((IneqContext)_localctx).R!=null?((IneqContext)_localctx).R.getText():null)));
		}
		return true;
	}

	public static final String _serializedATN =
		"\u0004\u0001\u0014\u008d\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001"+
		"\u0002\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004"+
		"\u0002\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007"+
		"\u0002\b\u0007\b\u0002\t\u0007\t\u0001\u0000\u0001\u0000\u0001\u0000\u0001"+
		"\u0000\u0001\u0000\u0003\u0000\u001a\b\u0000\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0003\u0001#\b"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0005\u0001(\b\u0001\n\u0001"+
		"\f\u0001+\t\u0001\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001"+
		"\u0002\u0001\u0002\u0005\u00023\b\u0002\n\u0002\f\u00026\t\u0002\u0001"+
		"\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001"+
		"\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0003\u0003C\b"+
		"\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0005\u0003H\b\u0003\n\u0003"+
		"\f\u0003K\t\u0003\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001"+
		"\u0004\u0001\u0004\u0005\u0004S\b\u0004\n\u0004\f\u0004V\t\u0004\u0001"+
		"\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0005"+
		"\u0005^\b\u0005\n\u0005\f\u0005a\t\u0005\u0001\u0006\u0001\u0006\u0001"+
		"\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001"+
		"\u0006\u0001\u0006\u0001\u0006\u0003\u0006n\b\u0006\u0001\u0007\u0001"+
		"\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0005\u0007v\b"+
		"\u0007\n\u0007\f\u0007y\t\u0007\u0001\b\u0001\b\u0001\b\u0001\b\u0001"+
		"\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0003\b\u0086\b\b\u0001"+
		"\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0000\u0006\u0002\u0004\u0006"+
		"\b\n\u000e\n\u0000\u0002\u0004\u0006\b\n\f\u000e\u0010\u0012\u0000\u0000"+
		"\u008e\u0000\u0019\u0001\u0000\u0000\u0000\u0002\"\u0001\u0000\u0000\u0000"+
		"\u0004,\u0001\u0000\u0000\u0000\u0006B\u0001\u0000\u0000\u0000\bL\u0001"+
		"\u0000\u0000\u0000\nW\u0001\u0000\u0000\u0000\fm\u0001\u0000\u0000\u0000"+
		"\u000eo\u0001\u0000\u0000\u0000\u0010\u0085\u0001\u0000\u0000\u0000\u0012"+
		"\u0087\u0001\u0000\u0000\u0000\u0014\u001a\u0003\u0002\u0001\u0000\u0015"+
		"\u0016\u0003\u0002\u0001\u0000\u0016\u0017\u0005\u0010\u0000\u0000\u0017"+
		"\u0018\u0003\u0002\u0001\u0000\u0018\u001a\u0001\u0000\u0000\u0000\u0019"+
		"\u0014\u0001\u0000\u0000\u0000\u0019\u0015\u0001\u0000\u0000\u0000\u001a"+
		"\u0001\u0001\u0000\u0000\u0000\u001b\u001c\u0006\u0001\uffff\uffff\u0000"+
		"\u001c#\u0003\u0004\u0002\u0000\u001d\u001e\u0003\u0006\u0003\u0000\u001e"+
		"\u001f\u0005\n\u0000\u0000\u001f \u0005\u0011\u0000\u0000 !\u0004\u0001"+
		"\u0000\u0001!#\u0001\u0000\u0000\u0000\"\u001b\u0001\u0000\u0000\u0000"+
		"\"\u001d\u0001\u0000\u0000\u0000#)\u0001\u0000\u0000\u0000$%\n\u0001\u0000"+
		"\u0000%&\u0005\f\u0000\u0000&(\u0003\u0002\u0001\u0002\'$\u0001\u0000"+
		"\u0000\u0000(+\u0001\u0000\u0000\u0000)\'\u0001\u0000\u0000\u0000)*\u0001"+
		"\u0000\u0000\u0000*\u0003\u0001\u0000\u0000\u0000+)\u0001\u0000\u0000"+
		"\u0000,-\u0006\u0002\uffff\uffff\u0000-.\u0003\u0006\u0003\u0000.4\u0001"+
		"\u0000\u0000\u0000/0\n\u0002\u0000\u000001\u0005\u000f\u0000\u000013\u0003"+
		"\u0006\u0003\u00002/\u0001\u0000\u0000\u000036\u0001\u0000\u0000\u0000"+
		"42\u0001\u0000\u0000\u000045\u0001\u0000\u0000\u00005\u0005\u0001\u0000"+
		"\u0000\u000064\u0001\u0000\u0000\u000078\u0006\u0003\uffff\uffff\u0000"+
		"89\u0005\u0006\u0000\u00009:\u0003\b\u0004\u0000:;\u0005\u000e\u0000\u0000"+
		";C\u0001\u0000\u0000\u0000<=\u0005\u0006\u0000\u0000=>\u0003\b\u0004\u0000"+
		">?\u0005\u0004\u0000\u0000?@\u0003\u000e\u0007\u0000@A\u0005\u000e\u0000"+
		"\u0000AC\u0001\u0000\u0000\u0000B7\u0001\u0000\u0000\u0000B<\u0001\u0000"+
		"\u0000\u0000CI\u0001\u0000\u0000\u0000DE\n\u0003\u0000\u0000EF\u0005\u0013"+
		"\u0000\u0000FH\u0003\u0006\u0003\u0004GD\u0001\u0000\u0000\u0000HK\u0001"+
		"\u0000\u0000\u0000IG\u0001\u0000\u0000\u0000IJ\u0001\u0000\u0000\u0000"+
		"J\u0007\u0001\u0000\u0000\u0000KI\u0001\u0000\u0000\u0000LM\u0006\u0004"+
		"\uffff\uffff\u0000MN\u0003\n\u0005\u0000NT\u0001\u0000\u0000\u0000OP\n"+
		"\u0001\u0000\u0000PQ\u0005\u0003\u0000\u0000QS\u0003\n\u0005\u0000RO\u0001"+
		"\u0000\u0000\u0000SV\u0001\u0000\u0000\u0000TR\u0001\u0000\u0000\u0000"+
		"TU\u0001\u0000\u0000\u0000U\t\u0001\u0000\u0000\u0000VT\u0001\u0000\u0000"+
		"\u0000WX\u0006\u0005\uffff\uffff\u0000XY\u0003\f\u0006\u0000Y_\u0001\u0000"+
		"\u0000\u0000Z[\n\u0001\u0000\u0000[\\\u0005\u0001\u0000\u0000\\^\u0003"+
		"\f\u0006\u0000]Z\u0001\u0000\u0000\u0000^a\u0001\u0000\u0000\u0000_]\u0001"+
		"\u0000\u0000\u0000_`\u0001\u0000\u0000\u0000`\u000b\u0001\u0000\u0000"+
		"\u0000a_\u0001\u0000\u0000\u0000bc\u0005\u0011\u0000\u0000cd\u0005\u0002"+
		"\u0000\u0000de\u0005\u0011\u0000\u0000en\u0005\r\u0000\u0000fg\u0005\u0011"+
		"\u0000\u0000gh\u0005\u0012\u0000\u0000hi\u0003\u000e\u0007\u0000ij\u0005"+
		"\u0002\u0000\u0000jk\u0005\u0011\u0000\u0000kl\u0005\r\u0000\u0000ln\u0001"+
		"\u0000\u0000\u0000mb\u0001\u0000\u0000\u0000mf\u0001\u0000\u0000\u0000"+
		"n\r\u0001\u0000\u0000\u0000op\u0006\u0007\uffff\uffff\u0000pq\u0003\u0010"+
		"\b\u0000qw\u0001\u0000\u0000\u0000rs\n\u0001\u0000\u0000st\u0005\u0003"+
		"\u0000\u0000tv\u0003\u0010\b\u0000ur\u0001\u0000\u0000\u0000vy\u0001\u0000"+
		"\u0000\u0000wu\u0001\u0000\u0000\u0000wx\u0001\u0000\u0000\u0000x\u000f"+
		"\u0001\u0000\u0000\u0000yw\u0001\u0000\u0000\u0000z{\u0005\u0002\u0000"+
		"\u0000{|\u0005\u0011\u0000\u0000|}\u0005\u0002\u0000\u0000}~\u0005\u0005"+
		"\u0000\u0000~\u007f\u0005\u0011\u0000\u0000\u007f\u0086\u0004\b\u0007"+
		"\u0001\u0080\u0081\u0005\u0011\u0000\u0000\u0081\u0082\u0005\u0005\u0000"+
		"\u0000\u0082\u0083\u0005\u0011\u0000\u0000\u0083\u0086\u0004\b\b\u0001"+
		"\u0084\u0086\u0003\u0012\t\u0000\u0085z\u0001\u0000\u0000\u0000\u0085"+
		"\u0080\u0001\u0000\u0000\u0000\u0085\u0084\u0001\u0000\u0000\u0000\u0086"+
		"\u0011\u0001\u0000\u0000\u0000\u0087\u0088\u0005\u0011\u0000\u0000\u0088"+
		"\u0089\u0005\u0007\u0000\u0000\u0089\u008a\u0005\u0011\u0000\u0000\u008a"+
		"\u008b\u0004\t\t\u0001\u008b\u0013\u0001\u0000\u0000\u0000\u000b\u0019"+
		"\")4BIT_mw\u0085";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}