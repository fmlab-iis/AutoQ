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
		ADD=1, BAR=2, COMMA=3, COLON=4, DIV=5, EQ=6, LEFT_PARENTHESIS=7, LEFT_BRACE=8, 
		MUL=9, NE=10, NEWLINES=11, OR=12, POWER=13, PRIME=14, PROD=15, RIGHT_ANGLE_BRACKET=16, 
		RIGHT_PARENTHESIS=17, RIGHT_BRACE=18, SEMICOLON=19, SETMINUS=20, STR=21, 
		SUB=22, SUM=23, UNION=24, WS=25;
	public static final int
		RULE_expr = 0, RULE_tset = 1, RULE_scset = 2, RULE_set = 3, RULE_diracs = 4, 
		RULE_dirac = 5, RULE_term = 6, RULE_complex = 7, RULE_angle = 8, RULE_varcons = 9, 
		RULE_varcon = 10, RULE_ineq = 11;
	private static String[] makeRuleNames() {
		return new String[] {
			"expr", "tset", "scset", "set", "diracs", "dirac", "term", "complex", 
			"angle", "varcons", "varcon", "ineq"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'+'", "'|'", "','", "':'", "'/'", "'='", "'('", "'{'", "'*'", 
			"'\\u2260'", null, "'\\u2228'", "'^'", "'''", "'\\u2297'", null, "')'", 
			"'}'", "';'", "'\\'", null, "'-'", null, "'\\u222A'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "ADD", "BAR", "COMMA", "COLON", "DIV", "EQ", "LEFT_PARENTHESIS", 
			"LEFT_BRACE", "MUL", "NE", "NEWLINES", "OR", "POWER", "PRIME", "PROD", 
			"RIGHT_ANGLE_BRACKET", "RIGHT_PARENTHESIS", "RIGHT_BRACE", "SEMICOLON", 
			"SETMINUS", "STR", "SUB", "SUM", "UNION", "WS"
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
	    std::set<std::string> predefinedConstants;

	    bool areAllDigits(const std::string& text) {
	        return std::all_of(text.begin(), text.end(), [](char c) { return '0' <= c && c <= '9'; });
	    }
	    bool isNonZero(const std::string& text) {
	        return areAllDigits(text) && std::stoi(text) != 0;
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
			setState(29);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,0,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(24);
				tset(0);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(25);
				tset(0);
				setState(26);
				match(SETMINUS);
				setState(27);
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
			setState(38);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,1,_ctx) ) {
			case 1:
				{
				setState(32);
				scset(0);
				}
				break;
			case 2:
				{
				setState(33);
				set(0);
				setState(34);
				match(POWER);
				setState(35);
				((TsetContext)_localctx).N = match(STR);
				setState(36);
				if (!( isNonZero((((TsetContext)_localctx).N!=null?((TsetContext)_localctx).N.getText():null)) )) throw new FailedPredicateException(this, " isNonZero($N.text) ");
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(45);
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
					setState(40);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(41);
					match(PROD);
					setState(42);
					tset(2);
					}
					} 
				}
				setState(47);
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
			setState(49);
			set(0);
			}
			_ctx.stop = _input.LT(-1);
			setState(56);
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
					setState(51);
					if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
					setState(52);
					match(SEMICOLON);
					setState(53);
					set(0);
					}
					} 
				}
				setState(58);
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
			setState(70);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,4,_ctx) ) {
			case 1:
				{
				setState(60);
				match(LEFT_BRACE);
				setState(61);
				diracs(0);
				setState(62);
				match(RIGHT_BRACE);
				}
				break;
			case 2:
				{
				setState(64);
				match(LEFT_BRACE);
				setState(65);
				diracs(0);
				setState(66);
				match(COLON);
				setState(67);
				varcons(0);
				setState(68);
				match(RIGHT_BRACE);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(77);
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
					setState(72);
					if (!(precpred(_ctx, 3))) throw new FailedPredicateException(this, "precpred(_ctx, 3)");
					setState(73);
					match(UNION);
					setState(74);
					set(4);
					}
					} 
				}
				setState(79);
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
			setState(81);
			dirac(0);
			}
			_ctx.stop = _input.LT(-1);
			setState(88);
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
					setState(83);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(84);
					match(COMMA);
					setState(85);
					dirac(0);
					}
					} 
				}
				setState(90);
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
		public TermContext term() {
			return getRuleContext(TermContext.class,0);
		}
		public DiracContext dirac() {
			return getRuleContext(DiracContext.class,0);
		}
		public TerminalNode ADD() { return getToken(ExtendedDiracParser.ADD, 0); }
		public TerminalNode SUB() { return getToken(ExtendedDiracParser.SUB, 0); }
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
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(92);
			term();
			}
			_ctx.stop = _input.LT(-1);
			setState(99);
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
					setState(94);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(95);
					_la = _input.LA(1);
					if ( !(_la==ADD || _la==SUB) ) {
					_errHandler.recoverInline(this);
					}
					else {
						if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
						_errHandler.reportMatch(this);
						consume();
					}
					setState(96);
					term();
					}
					} 
				}
				setState(101);
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
		public Token VStr;
		public TerminalNode BAR() { return getToken(ExtendedDiracParser.BAR, 0); }
		public TerminalNode RIGHT_ANGLE_BRACKET() { return getToken(ExtendedDiracParser.RIGHT_ANGLE_BRACKET, 0); }
		public TerminalNode STR() { return getToken(ExtendedDiracParser.STR, 0); }
		public ComplexContext complex() {
			return getRuleContext(ComplexContext.class,0);
		}
		public TerminalNode SUM() { return getToken(ExtendedDiracParser.SUM, 0); }
		public VarconsContext varcons() {
			return getRuleContext(VarconsContext.class,0);
		}
		public TerminalNode SUB() { return getToken(ExtendedDiracParser.SUB, 0); }
		public TermContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_term; }
	}

	public final TermContext term() throws RecognitionException {
		TermContext _localctx = new TermContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_term);
		int _la;
		try {
			setState(128);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,10,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(103);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & 6291584L) != 0)) {
					{
					setState(102);
					complex(0);
					}
				}

				setState(105);
				match(BAR);
				setState(106);
				((TermContext)_localctx).VStr = match(STR);
				setState(107);
				match(RIGHT_ANGLE_BRACKET);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(109);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & 6291584L) != 0)) {
					{
					setState(108);
					complex(0);
					}
				}

				setState(111);
				match(SUM);
				setState(112);
				varcons(0);
				setState(113);
				match(BAR);
				setState(114);
				((TermContext)_localctx).VStr = match(STR);
				setState(115);
				match(RIGHT_ANGLE_BRACKET);
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(117);
				match(SUB);
				setState(118);
				match(BAR);
				setState(119);
				((TermContext)_localctx).VStr = match(STR);
				setState(120);
				match(RIGHT_ANGLE_BRACKET);
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(121);
				match(SUB);
				setState(122);
				match(SUM);
				setState(123);
				varcons(0);
				setState(124);
				match(BAR);
				setState(125);
				((TermContext)_localctx).VStr = match(STR);
				setState(126);
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
	public static class ComplexContext extends ParserRuleContext {
		public Token sub;
		public Token eixpi;
		public Token var;
		public Token op;
		public Token n;
		public List<ComplexContext> complex() {
			return getRuleContexts(ComplexContext.class);
		}
		public ComplexContext complex(int i) {
			return getRuleContext(ComplexContext.class,i);
		}
		public TerminalNode SUB() { return getToken(ExtendedDiracParser.SUB, 0); }
		public TerminalNode LEFT_PARENTHESIS() { return getToken(ExtendedDiracParser.LEFT_PARENTHESIS, 0); }
		public TerminalNode RIGHT_PARENTHESIS() { return getToken(ExtendedDiracParser.RIGHT_PARENTHESIS, 0); }
		public AngleContext angle() {
			return getRuleContext(AngleContext.class,0);
		}
		public TerminalNode STR() { return getToken(ExtendedDiracParser.STR, 0); }
		public TerminalNode MUL() { return getToken(ExtendedDiracParser.MUL, 0); }
		public TerminalNode DIV() { return getToken(ExtendedDiracParser.DIV, 0); }
		public TerminalNode ADD() { return getToken(ExtendedDiracParser.ADD, 0); }
		public TerminalNode POWER() { return getToken(ExtendedDiracParser.POWER, 0); }
		public ComplexContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_complex; }
	}

	public final ComplexContext complex() throws RecognitionException {
		return complex(0);
	}

	private ComplexContext complex(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		ComplexContext _localctx = new ComplexContext(_ctx, _parentState);
		ComplexContext _prevctx = _localctx;
		int _startState = 14;
		enterRecursionRule(_localctx, 14, RULE_complex, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(144);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,11,_ctx) ) {
			case 1:
				{
				setState(131);
				((ComplexContext)_localctx).sub = match(SUB);
				setState(132);
				complex(6);
				}
				break;
			case 2:
				{
				setState(133);
				match(LEFT_PARENTHESIS);
				setState(134);
				complex(0);
				setState(135);
				match(RIGHT_PARENTHESIS);
				}
				break;
			case 3:
				{
				setState(137);
				((ComplexContext)_localctx).eixpi = match(STR);
				setState(138);
				match(LEFT_PARENTHESIS);
				setState(139);
				angle();
				setState(140);
				match(RIGHT_PARENTHESIS);
				setState(141);
				if (!( (((ComplexContext)_localctx).eixpi!=null?((ComplexContext)_localctx).eixpi.getText():null) == "eipi" || (((ComplexContext)_localctx).eixpi!=null?((ComplexContext)_localctx).eixpi.getText():null) == "ei2pi" )) throw new FailedPredicateException(this, " $eixpi.text == \"eipi\" || $eixpi.text == \"ei2pi\" ");
				}
				break;
			case 4:
				{
				setState(143);
				((ComplexContext)_localctx).var = match(STR);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(158);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,13,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(156);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,12,_ctx) ) {
					case 1:
						{
						_localctx = new ComplexContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_complex);
						setState(146);
						if (!(precpred(_ctx, 5))) throw new FailedPredicateException(this, "precpred(_ctx, 5)");
						setState(147);
						((ComplexContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==DIV || _la==MUL) ) {
							((ComplexContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(148);
						complex(6);
						}
						break;
					case 2:
						{
						_localctx = new ComplexContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_complex);
						setState(149);
						if (!(precpred(_ctx, 4))) throw new FailedPredicateException(this, "precpred(_ctx, 4)");
						setState(150);
						((ComplexContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==ADD || _la==SUB) ) {
							((ComplexContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(151);
						complex(5);
						}
						break;
					case 3:
						{
						_localctx = new ComplexContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_complex);
						setState(152);
						if (!(precpred(_ctx, 7))) throw new FailedPredicateException(this, "precpred(_ctx, 7)");
						setState(153);
						match(POWER);
						setState(154);
						((ComplexContext)_localctx).n = match(STR);
						setState(155);
						if (!( isNonZero((((ComplexContext)_localctx).n!=null?((ComplexContext)_localctx).n.getText():null)) )) throw new FailedPredicateException(this, " isNonZero($n.text) ");
						}
						break;
					}
					} 
				}
				setState(160);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,13,_ctx);
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
	public static class AngleContext extends ParserRuleContext {
		public Token x;
		public Token y;
		public Token n;
		public TerminalNode DIV() { return getToken(ExtendedDiracParser.DIV, 0); }
		public List<TerminalNode> STR() { return getTokens(ExtendedDiracParser.STR); }
		public TerminalNode STR(int i) {
			return getToken(ExtendedDiracParser.STR, i);
		}
		public TerminalNode SUB() { return getToken(ExtendedDiracParser.SUB, 0); }
		public AngleContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_angle; }
	}

	public final AngleContext angle() throws RecognitionException {
		AngleContext _localctx = new AngleContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_angle);
		int _la;
		try {
			setState(173);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,16,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(162);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==SUB) {
					{
					setState(161);
					match(SUB);
					}
				}

				setState(164);
				((AngleContext)_localctx).x = match(STR);
				setState(165);
				match(DIV);
				setState(166);
				((AngleContext)_localctx).y = match(STR);
				setState(167);
				if (!( areAllDigits((((AngleContext)_localctx).x!=null?((AngleContext)_localctx).x.getText():null)) && isNonZero((((AngleContext)_localctx).y!=null?((AngleContext)_localctx).y.getText():null)) )) throw new FailedPredicateException(this, " areAllDigits($x.text) && isNonZero($y.text) ");
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(169);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==SUB) {
					{
					setState(168);
					match(SUB);
					}
				}

				setState(171);
				((AngleContext)_localctx).n = match(STR);
				setState(172);
				if (!( areAllDigits((((AngleContext)_localctx).n!=null?((AngleContext)_localctx).n.getText():null)) )) throw new FailedPredicateException(this, " areAllDigits($n.text) ");
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
		int _startState = 18;
		enterRecursionRule(_localctx, 18, RULE_varcons, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(176);
			varcon();
			}
			_ctx.stop = _input.LT(-1);
			setState(183);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,17,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new VarconsContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_varcons);
					setState(178);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(179);
					match(COMMA);
					setState(180);
					varcon();
					}
					} 
				}
				setState(185);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,17,_ctx);
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
		enterRule(_localctx, 20, RULE_varcon);
		try {
			setState(197);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,18,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(186);
				match(BAR);
				setState(187);
				((VarconContext)_localctx).V = match(STR);
				setState(188);
				match(BAR);
				setState(189);
				match(EQ);
				setState(190);
				((VarconContext)_localctx).N = match(STR);
				setState(191);
				if (!( isALowercaseLetter((((VarconContext)_localctx).V!=null?((VarconContext)_localctx).V.getText():null)) && isNonZero((((VarconContext)_localctx).N!=null?((VarconContext)_localctx).N.getText():null)) )) throw new FailedPredicateException(this, " isALowercaseLetter($V.text) && isNonZero($N.text) ");
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(192);
				((VarconContext)_localctx).V = match(STR);
				setState(193);
				match(EQ);
				setState(194);
				((VarconContext)_localctx).CStr = match(STR);
				setState(195);
				if (!( isALowercaseLetter((((VarconContext)_localctx).V!=null?((VarconContext)_localctx).V.getText():null)) && isAConstantBinaryString((((VarconContext)_localctx).CStr!=null?((VarconContext)_localctx).CStr.getText():null)) )) throw new FailedPredicateException(this, " isALowercaseLetter($V.text) && isAConstantBinaryString($CStr.text) ");
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(196);
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
		enterRule(_localctx, 22, RULE_ineq);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(199);
			((IneqContext)_localctx).L = match(STR);
			setState(200);
			match(NE);
			setState(201);
			((IneqContext)_localctx).R = match(STR);
			setState(202);
			if (!( isALowercaseLetter((((IneqContext)_localctx).L!=null?((IneqContext)_localctx).L.getText():null)) && (isALowercaseLetter((((IneqContext)_localctx).R!=null?((IneqContext)_localctx).R.getText():null)) || isAConstantBinaryString((((IneqContext)_localctx).R!=null?((IneqContext)_localctx).R.getText():null))) )) throw new FailedPredicateException(this, " isALowercaseLetter($L.text) && (isALowercaseLetter($R.text) || isAConstantBinaryString($R.text)) ");
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
			return complex_sempred((ComplexContext)_localctx, predIndex);
		case 8:
			return angle_sempred((AngleContext)_localctx, predIndex);
		case 9:
			return varcons_sempred((VarconsContext)_localctx, predIndex);
		case 10:
			return varcon_sempred((VarconContext)_localctx, predIndex);
		case 11:
			return ineq_sempred((IneqContext)_localctx, predIndex);
		}
		return true;
	}
	private boolean tset_sempred(TsetContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return  isNonZero((((TsetContext)_localctx).N!=null?((TsetContext)_localctx).N.getText():null)) ;
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
	private boolean complex_sempred(ComplexContext _localctx, int predIndex) {
		switch (predIndex) {
		case 6:
			return  (((ComplexContext)_localctx).eixpi!=null?((ComplexContext)_localctx).eixpi.getText():null) == "eipi" || (((ComplexContext)_localctx).eixpi!=null?((ComplexContext)_localctx).eixpi.getText():null) == "ei2pi" ;
		case 7:
			return precpred(_ctx, 5);
		case 8:
			return precpred(_ctx, 4);
		case 9:
			return precpred(_ctx, 7);
		case 10:
			return  isNonZero((((ComplexContext)_localctx).n!=null?((ComplexContext)_localctx).n.getText():null)) ;
		}
		return true;
	}
	private boolean angle_sempred(AngleContext _localctx, int predIndex) {
		switch (predIndex) {
		case 11:
			return  areAllDigits((((AngleContext)_localctx).x!=null?((AngleContext)_localctx).x.getText():null)) && isNonZero((((AngleContext)_localctx).y!=null?((AngleContext)_localctx).y.getText():null)) ;
		case 12:
			return  areAllDigits((((AngleContext)_localctx).n!=null?((AngleContext)_localctx).n.getText():null)) ;
		}
		return true;
	}
	private boolean varcons_sempred(VarconsContext _localctx, int predIndex) {
		switch (predIndex) {
		case 13:
			return precpred(_ctx, 1);
		}
		return true;
	}
	private boolean varcon_sempred(VarconContext _localctx, int predIndex) {
		switch (predIndex) {
		case 14:
			return  isALowercaseLetter((((VarconContext)_localctx).V!=null?((VarconContext)_localctx).V.getText():null)) && isNonZero((((VarconContext)_localctx).N!=null?((VarconContext)_localctx).N.getText():null)) ;
		case 15:
			return  isALowercaseLetter((((VarconContext)_localctx).V!=null?((VarconContext)_localctx).V.getText():null)) && isAConstantBinaryString((((VarconContext)_localctx).CStr!=null?((VarconContext)_localctx).CStr.getText():null)) ;
		}
		return true;
	}
	private boolean ineq_sempred(IneqContext _localctx, int predIndex) {
		switch (predIndex) {
		case 16:
			return  isALowercaseLetter((((IneqContext)_localctx).L!=null?((IneqContext)_localctx).L.getText():null)) && (isALowercaseLetter((((IneqContext)_localctx).R!=null?((IneqContext)_localctx).R.getText():null)) || isAConstantBinaryString((((IneqContext)_localctx).R!=null?((IneqContext)_localctx).R.getText():null))) ;
		}
		return true;
	}

	public static final String _serializedATN =
		"\u0004\u0001\u0019\u00cd\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001"+
		"\u0002\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004"+
		"\u0002\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007"+
		"\u0002\b\u0007\b\u0002\t\u0007\t\u0002\n\u0007\n\u0002\u000b\u0007\u000b"+
		"\u0001\u0000\u0001\u0000\u0001\u0000\u0001\u0000\u0001\u0000\u0003\u0000"+
		"\u001e\b\u0000\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0003\u0001\'\b\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0005\u0001,\b\u0001\n\u0001\f\u0001/\t\u0001\u0001\u0002"+
		"\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0005\u0002"+
		"7\b\u0002\n\u0002\f\u0002:\t\u0002\u0001\u0003\u0001\u0003\u0001\u0003"+
		"\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003"+
		"\u0001\u0003\u0001\u0003\u0003\u0003G\b\u0003\u0001\u0003\u0001\u0003"+
		"\u0001\u0003\u0005\u0003L\b\u0003\n\u0003\f\u0003O\t\u0003\u0001\u0004"+
		"\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0005\u0004"+
		"W\b\u0004\n\u0004\f\u0004Z\t\u0004\u0001\u0005\u0001\u0005\u0001\u0005"+
		"\u0001\u0005\u0001\u0005\u0001\u0005\u0005\u0005b\b\u0005\n\u0005\f\u0005"+
		"e\t\u0005\u0001\u0006\u0003\u0006h\b\u0006\u0001\u0006\u0001\u0006\u0001"+
		"\u0006\u0001\u0006\u0003\u0006n\b\u0006\u0001\u0006\u0001\u0006\u0001"+
		"\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001"+
		"\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001"+
		"\u0006\u0001\u0006\u0001\u0006\u0003\u0006\u0081\b\u0006\u0001\u0007\u0001"+
		"\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001"+
		"\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001"+
		"\u0007\u0003\u0007\u0091\b\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001"+
		"\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001"+
		"\u0007\u0005\u0007\u009d\b\u0007\n\u0007\f\u0007\u00a0\t\u0007\u0001\b"+
		"\u0003\b\u00a3\b\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0003\b\u00aa"+
		"\b\b\u0001\b\u0001\b\u0003\b\u00ae\b\b\u0001\t\u0001\t\u0001\t\u0001\t"+
		"\u0001\t\u0001\t\u0005\t\u00b6\b\t\n\t\f\t\u00b9\t\t\u0001\n\u0001\n\u0001"+
		"\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n\u0003"+
		"\n\u00c6\b\n\u0001\u000b\u0001\u000b\u0001\u000b\u0001\u000b\u0001\u000b"+
		"\u0001\u000b\u0000\u0007\u0002\u0004\u0006\b\n\u000e\u0012\f\u0000\u0002"+
		"\u0004\u0006\b\n\f\u000e\u0010\u0012\u0014\u0016\u0000\u0002\u0002\u0000"+
		"\u0001\u0001\u0016\u0016\u0002\u0000\u0005\u0005\t\t\u00d9\u0000\u001d"+
		"\u0001\u0000\u0000\u0000\u0002&\u0001\u0000\u0000\u0000\u00040\u0001\u0000"+
		"\u0000\u0000\u0006F\u0001\u0000\u0000\u0000\bP\u0001\u0000\u0000\u0000"+
		"\n[\u0001\u0000\u0000\u0000\f\u0080\u0001\u0000\u0000\u0000\u000e\u0090"+
		"\u0001\u0000\u0000\u0000\u0010\u00ad\u0001\u0000\u0000\u0000\u0012\u00af"+
		"\u0001\u0000\u0000\u0000\u0014\u00c5\u0001\u0000\u0000\u0000\u0016\u00c7"+
		"\u0001\u0000\u0000\u0000\u0018\u001e\u0003\u0002\u0001\u0000\u0019\u001a"+
		"\u0003\u0002\u0001\u0000\u001a\u001b\u0005\u0014\u0000\u0000\u001b\u001c"+
		"\u0003\u0002\u0001\u0000\u001c\u001e\u0001\u0000\u0000\u0000\u001d\u0018"+
		"\u0001\u0000\u0000\u0000\u001d\u0019\u0001\u0000\u0000\u0000\u001e\u0001"+
		"\u0001\u0000\u0000\u0000\u001f \u0006\u0001\uffff\uffff\u0000 \'\u0003"+
		"\u0004\u0002\u0000!\"\u0003\u0006\u0003\u0000\"#\u0005\r\u0000\u0000#"+
		"$\u0005\u0015\u0000\u0000$%\u0004\u0001\u0000\u0001%\'\u0001\u0000\u0000"+
		"\u0000&\u001f\u0001\u0000\u0000\u0000&!\u0001\u0000\u0000\u0000\'-\u0001"+
		"\u0000\u0000\u0000()\n\u0001\u0000\u0000)*\u0005\u000f\u0000\u0000*,\u0003"+
		"\u0002\u0001\u0002+(\u0001\u0000\u0000\u0000,/\u0001\u0000\u0000\u0000"+
		"-+\u0001\u0000\u0000\u0000-.\u0001\u0000\u0000\u0000.\u0003\u0001\u0000"+
		"\u0000\u0000/-\u0001\u0000\u0000\u000001\u0006\u0002\uffff\uffff\u0000"+
		"12\u0003\u0006\u0003\u000028\u0001\u0000\u0000\u000034\n\u0002\u0000\u0000"+
		"45\u0005\u0013\u0000\u000057\u0003\u0006\u0003\u000063\u0001\u0000\u0000"+
		"\u00007:\u0001\u0000\u0000\u000086\u0001\u0000\u0000\u000089\u0001\u0000"+
		"\u0000\u00009\u0005\u0001\u0000\u0000\u0000:8\u0001\u0000\u0000\u0000"+
		";<\u0006\u0003\uffff\uffff\u0000<=\u0005\b\u0000\u0000=>\u0003\b\u0004"+
		"\u0000>?\u0005\u0012\u0000\u0000?G\u0001\u0000\u0000\u0000@A\u0005\b\u0000"+
		"\u0000AB\u0003\b\u0004\u0000BC\u0005\u0004\u0000\u0000CD\u0003\u0012\t"+
		"\u0000DE\u0005\u0012\u0000\u0000EG\u0001\u0000\u0000\u0000F;\u0001\u0000"+
		"\u0000\u0000F@\u0001\u0000\u0000\u0000GM\u0001\u0000\u0000\u0000HI\n\u0003"+
		"\u0000\u0000IJ\u0005\u0018\u0000\u0000JL\u0003\u0006\u0003\u0004KH\u0001"+
		"\u0000\u0000\u0000LO\u0001\u0000\u0000\u0000MK\u0001\u0000\u0000\u0000"+
		"MN\u0001\u0000\u0000\u0000N\u0007\u0001\u0000\u0000\u0000OM\u0001\u0000"+
		"\u0000\u0000PQ\u0006\u0004\uffff\uffff\u0000QR\u0003\n\u0005\u0000RX\u0001"+
		"\u0000\u0000\u0000ST\n\u0001\u0000\u0000TU\u0005\u0003\u0000\u0000UW\u0003"+
		"\n\u0005\u0000VS\u0001\u0000\u0000\u0000WZ\u0001\u0000\u0000\u0000XV\u0001"+
		"\u0000\u0000\u0000XY\u0001\u0000\u0000\u0000Y\t\u0001\u0000\u0000\u0000"+
		"ZX\u0001\u0000\u0000\u0000[\\\u0006\u0005\uffff\uffff\u0000\\]\u0003\f"+
		"\u0006\u0000]c\u0001\u0000\u0000\u0000^_\n\u0001\u0000\u0000_`\u0007\u0000"+
		"\u0000\u0000`b\u0003\f\u0006\u0000a^\u0001\u0000\u0000\u0000be\u0001\u0000"+
		"\u0000\u0000ca\u0001\u0000\u0000\u0000cd\u0001\u0000\u0000\u0000d\u000b"+
		"\u0001\u0000\u0000\u0000ec\u0001\u0000\u0000\u0000fh\u0003\u000e\u0007"+
		"\u0000gf\u0001\u0000\u0000\u0000gh\u0001\u0000\u0000\u0000hi\u0001\u0000"+
		"\u0000\u0000ij\u0005\u0002\u0000\u0000jk\u0005\u0015\u0000\u0000k\u0081"+
		"\u0005\u0010\u0000\u0000ln\u0003\u000e\u0007\u0000ml\u0001\u0000\u0000"+
		"\u0000mn\u0001\u0000\u0000\u0000no\u0001\u0000\u0000\u0000op\u0005\u0017"+
		"\u0000\u0000pq\u0003\u0012\t\u0000qr\u0005\u0002\u0000\u0000rs\u0005\u0015"+
		"\u0000\u0000st\u0005\u0010\u0000\u0000t\u0081\u0001\u0000\u0000\u0000"+
		"uv\u0005\u0016\u0000\u0000vw\u0005\u0002\u0000\u0000wx\u0005\u0015\u0000"+
		"\u0000x\u0081\u0005\u0010\u0000\u0000yz\u0005\u0016\u0000\u0000z{\u0005"+
		"\u0017\u0000\u0000{|\u0003\u0012\t\u0000|}\u0005\u0002\u0000\u0000}~\u0005"+
		"\u0015\u0000\u0000~\u007f\u0005\u0010\u0000\u0000\u007f\u0081\u0001\u0000"+
		"\u0000\u0000\u0080g\u0001\u0000\u0000\u0000\u0080m\u0001\u0000\u0000\u0000"+
		"\u0080u\u0001\u0000\u0000\u0000\u0080y\u0001\u0000\u0000\u0000\u0081\r"+
		"\u0001\u0000\u0000\u0000\u0082\u0083\u0006\u0007\uffff\uffff\u0000\u0083"+
		"\u0084\u0005\u0016\u0000\u0000\u0084\u0091\u0003\u000e\u0007\u0006\u0085"+
		"\u0086\u0005\u0007\u0000\u0000\u0086\u0087\u0003\u000e\u0007\u0000\u0087"+
		"\u0088\u0005\u0011\u0000\u0000\u0088\u0091\u0001\u0000\u0000\u0000\u0089"+
		"\u008a\u0005\u0015\u0000\u0000\u008a\u008b\u0005\u0007\u0000\u0000\u008b"+
		"\u008c\u0003\u0010\b\u0000\u008c\u008d\u0005\u0011\u0000\u0000\u008d\u008e"+
		"\u0004\u0007\u0006\u0001\u008e\u0091\u0001\u0000\u0000\u0000\u008f\u0091"+
		"\u0005\u0015\u0000\u0000\u0090\u0082\u0001\u0000\u0000\u0000\u0090\u0085"+
		"\u0001\u0000\u0000\u0000\u0090\u0089\u0001\u0000\u0000\u0000\u0090\u008f"+
		"\u0001\u0000\u0000\u0000\u0091\u009e\u0001\u0000\u0000\u0000\u0092\u0093"+
		"\n\u0005\u0000\u0000\u0093\u0094\u0007\u0001\u0000\u0000\u0094\u009d\u0003"+
		"\u000e\u0007\u0006\u0095\u0096\n\u0004\u0000\u0000\u0096\u0097\u0007\u0000"+
		"\u0000\u0000\u0097\u009d\u0003\u000e\u0007\u0005\u0098\u0099\n\u0007\u0000"+
		"\u0000\u0099\u009a\u0005\r\u0000\u0000\u009a\u009b\u0005\u0015\u0000\u0000"+
		"\u009b\u009d\u0004\u0007\n\u0001\u009c\u0092\u0001\u0000\u0000\u0000\u009c"+
		"\u0095\u0001\u0000\u0000\u0000\u009c\u0098\u0001\u0000\u0000\u0000\u009d"+
		"\u00a0\u0001\u0000\u0000\u0000\u009e\u009c\u0001\u0000\u0000\u0000\u009e"+
		"\u009f\u0001\u0000\u0000\u0000\u009f\u000f\u0001\u0000\u0000\u0000\u00a0"+
		"\u009e\u0001\u0000\u0000\u0000\u00a1\u00a3\u0005\u0016\u0000\u0000\u00a2"+
		"\u00a1\u0001\u0000\u0000\u0000\u00a2\u00a3\u0001\u0000\u0000\u0000\u00a3"+
		"\u00a4\u0001\u0000\u0000\u0000\u00a4\u00a5\u0005\u0015\u0000\u0000\u00a5"+
		"\u00a6\u0005\u0005\u0000\u0000\u00a6\u00a7\u0005\u0015\u0000\u0000\u00a7"+
		"\u00ae\u0004\b\u000b\u0001\u00a8\u00aa\u0005\u0016\u0000\u0000\u00a9\u00a8"+
		"\u0001\u0000\u0000\u0000\u00a9\u00aa\u0001\u0000\u0000\u0000\u00aa\u00ab"+
		"\u0001\u0000\u0000\u0000\u00ab\u00ac\u0005\u0015\u0000\u0000\u00ac\u00ae"+
		"\u0004\b\f\u0001\u00ad\u00a2\u0001\u0000\u0000\u0000\u00ad\u00a9\u0001"+
		"\u0000\u0000\u0000\u00ae\u0011\u0001\u0000\u0000\u0000\u00af\u00b0\u0006"+
		"\t\uffff\uffff\u0000\u00b0\u00b1\u0003\u0014\n\u0000\u00b1\u00b7\u0001"+
		"\u0000\u0000\u0000\u00b2\u00b3\n\u0001\u0000\u0000\u00b3\u00b4\u0005\u0003"+
		"\u0000\u0000\u00b4\u00b6\u0003\u0014\n\u0000\u00b5\u00b2\u0001\u0000\u0000"+
		"\u0000\u00b6\u00b9\u0001\u0000\u0000\u0000\u00b7\u00b5\u0001\u0000\u0000"+
		"\u0000\u00b7\u00b8\u0001\u0000\u0000\u0000\u00b8\u0013\u0001\u0000\u0000"+
		"\u0000\u00b9\u00b7\u0001\u0000\u0000\u0000\u00ba\u00bb\u0005\u0002\u0000"+
		"\u0000\u00bb\u00bc\u0005\u0015\u0000\u0000\u00bc\u00bd\u0005\u0002\u0000"+
		"\u0000\u00bd\u00be\u0005\u0006\u0000\u0000\u00be\u00bf\u0005\u0015\u0000"+
		"\u0000\u00bf\u00c6\u0004\n\u000e\u0001\u00c0\u00c1\u0005\u0015\u0000\u0000"+
		"\u00c1\u00c2\u0005\u0006\u0000\u0000\u00c2\u00c3\u0005\u0015\u0000\u0000"+
		"\u00c3\u00c6\u0004\n\u000f\u0001\u00c4\u00c6\u0003\u0016\u000b\u0000\u00c5"+
		"\u00ba\u0001\u0000\u0000\u0000\u00c5\u00c0\u0001\u0000\u0000\u0000\u00c5"+
		"\u00c4\u0001\u0000\u0000\u0000\u00c6\u0015\u0001\u0000\u0000\u0000\u00c7"+
		"\u00c8\u0005\u0015\u0000\u0000\u00c8\u00c9\u0005\n\u0000\u0000\u00c9\u00ca"+
		"\u0005\u0015\u0000\u0000\u00ca\u00cb\u0004\u000b\u0010\u0001\u00cb\u0017"+
		"\u0001\u0000\u0000\u0000\u0013\u001d&-8FMXcgm\u0080\u0090\u009c\u009e"+
		"\u00a2\u00a9\u00ad\u00b7\u00c5";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}