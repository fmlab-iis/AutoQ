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
		MUL=9, NE=10, NEWLINES=11, POWER=12, PRIME=13, PROD=14, RIGHT_ANGLE_BRACKET=15, 
		RIGHT_PARENTHESIS=16, RIGHT_BRACE=17, SEMICOLON=18, SETMINUS=19, STR=20, 
		SUB=21, SUM=22, UNION=23, WS=24, LOGICAL_AND=25, LOGICAL_OR=26, LOGICAL_NOT=27, 
		LESS_THAN=28, LESS_EQUAL=29, GREATER_EQUAL=30;
	public static final int
		RULE_expr = 0, RULE_tset = 1, RULE_scset = 2, RULE_set = 3, RULE_diracs = 4, 
		RULE_dirac = 5, RULE_term = 6, RULE_complex = 7, RULE_angle = 8, RULE_varcons = 9, 
		RULE_varcon = 10, RULE_eq = 11, RULE_ineq = 12, RULE_predicate = 13;
	private static String[] makeRuleNames() {
		return new String[] {
			"expr", "tset", "scset", "set", "diracs", "dirac", "term", "complex", 
			"angle", "varcons", "varcon", "eq", "ineq", "predicate"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'+'", "'|'", "','", "':'", "'/'", "'='", "'('", "'{'", "'*'", 
			"'\\u2260'", null, "'^'", "'''", "'\\u2297'", null, "')'", "'}'", "';'", 
			"'\\'", null, "'-'", null, "'\\u222A'", null, null, null, null, "'<'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "ADD", "BAR", "COMMA", "COLON", "DIV", "EQ", "LEFT_PARENTHESIS", 
			"LEFT_BRACE", "MUL", "NE", "NEWLINES", "POWER", "PRIME", "PROD", "RIGHT_ANGLE_BRACKET", 
			"RIGHT_PARENTHESIS", "RIGHT_BRACE", "SEMICOLON", "SETMINUS", "STR", "SUB", 
			"SUM", "UNION", "WS", "LOGICAL_AND", "LOGICAL_OR", "LOGICAL_NOT", "LESS_THAN", 
			"LESS_EQUAL", "GREATER_EQUAL"
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
			setState(33);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,0,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(28);
				tset(0);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(29);
				tset(0);
				setState(30);
				match(SETMINUS);
				setState(31);
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
			setState(42);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,1,_ctx) ) {
			case 1:
				{
				setState(36);
				scset(0);
				}
				break;
			case 2:
				{
				setState(37);
				set(0);
				setState(38);
				match(POWER);
				setState(39);
				((TsetContext)_localctx).N = match(STR);
				setState(40);
				if (!( isNonZero((((TsetContext)_localctx).N!=null?((TsetContext)_localctx).N.getText():null)) )) throw new FailedPredicateException(this, " isNonZero($N.text) ");
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(49);
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
					setState(44);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(45);
					match(PROD);
					setState(46);
					tset(2);
					}
					} 
				}
				setState(51);
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
			setState(53);
			set(0);
			}
			_ctx.stop = _input.LT(-1);
			setState(60);
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
					setState(55);
					if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
					setState(56);
					match(SEMICOLON);
					setState(57);
					set(0);
					}
					} 
				}
				setState(62);
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
			setState(74);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,4,_ctx) ) {
			case 1:
				{
				setState(64);
				match(LEFT_BRACE);
				setState(65);
				diracs(0);
				setState(66);
				match(RIGHT_BRACE);
				}
				break;
			case 2:
				{
				setState(68);
				match(LEFT_BRACE);
				setState(69);
				diracs(0);
				setState(70);
				match(COLON);
				setState(71);
				varcons(0);
				setState(72);
				match(RIGHT_BRACE);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(81);
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
					setState(76);
					if (!(precpred(_ctx, 3))) throw new FailedPredicateException(this, "precpred(_ctx, 3)");
					setState(77);
					match(UNION);
					setState(78);
					set(4);
					}
					} 
				}
				setState(83);
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
			setState(85);
			dirac(0);
			}
			_ctx.stop = _input.LT(-1);
			setState(92);
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
					setState(87);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(88);
					match(COMMA);
					setState(89);
					dirac(0);
					}
					} 
				}
				setState(94);
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
			setState(96);
			term();
			}
			_ctx.stop = _input.LT(-1);
			setState(103);
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
					setState(98);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(99);
					_la = _input.LA(1);
					if ( !(_la==ADD || _la==SUB) ) {
					_errHandler.recoverInline(this);
					}
					else {
						if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
						_errHandler.reportMatch(this);
						consume();
					}
					setState(100);
					term();
					}
					} 
				}
				setState(105);
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
			setState(132);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,10,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(107);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & 3145856L) != 0)) {
					{
					setState(106);
					complex(0);
					}
				}

				setState(109);
				match(BAR);
				setState(110);
				((TermContext)_localctx).VStr = match(STR);
				setState(111);
				match(RIGHT_ANGLE_BRACKET);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(113);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & 3145856L) != 0)) {
					{
					setState(112);
					complex(0);
					}
				}

				setState(115);
				match(SUM);
				setState(116);
				varcons(0);
				setState(117);
				match(BAR);
				setState(118);
				((TermContext)_localctx).VStr = match(STR);
				setState(119);
				match(RIGHT_ANGLE_BRACKET);
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(121);
				match(SUB);
				setState(122);
				match(BAR);
				setState(123);
				((TermContext)_localctx).VStr = match(STR);
				setState(124);
				match(RIGHT_ANGLE_BRACKET);
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(125);
				match(SUB);
				setState(126);
				match(SUM);
				setState(127);
				varcons(0);
				setState(128);
				match(BAR);
				setState(129);
				((TermContext)_localctx).VStr = match(STR);
				setState(130);
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
		public Token func;
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
			setState(148);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,11,_ctx) ) {
			case 1:
				{
				setState(135);
				((ComplexContext)_localctx).sub = match(SUB);
				setState(136);
				complex(6);
				}
				break;
			case 2:
				{
				setState(137);
				match(LEFT_PARENTHESIS);
				setState(138);
				complex(0);
				setState(139);
				match(RIGHT_PARENTHESIS);
				}
				break;
			case 3:
				{
				setState(141);
				((ComplexContext)_localctx).func = match(STR);
				setState(142);
				match(LEFT_PARENTHESIS);
				setState(143);
				complex(0);
				setState(144);
				match(RIGHT_PARENTHESIS);
				setState(145);
				if (!( (((ComplexContext)_localctx).func!=null?((ComplexContext)_localctx).func.getText():null) == "real" || (((ComplexContext)_localctx).func!=null?((ComplexContext)_localctx).func.getText():null) == "imag" || (((ComplexContext)_localctx).func!=null?((ComplexContext)_localctx).func.getText():null) == "eipi" || (((ComplexContext)_localctx).func!=null?((ComplexContext)_localctx).func.getText():null) == "ei2pi" )) throw new FailedPredicateException(this, " $func.text == \"real\" || $func.text == \"imag\" || $func.text == \"eipi\" || $func.text == \"ei2pi\" ");
				}
				break;
			case 4:
				{
				setState(147);
				((ComplexContext)_localctx).var = match(STR);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(162);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,13,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(160);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,12,_ctx) ) {
					case 1:
						{
						_localctx = new ComplexContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_complex);
						setState(150);
						if (!(precpred(_ctx, 5))) throw new FailedPredicateException(this, "precpred(_ctx, 5)");
						setState(151);
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
						setState(152);
						complex(6);
						}
						break;
					case 2:
						{
						_localctx = new ComplexContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_complex);
						setState(153);
						if (!(precpred(_ctx, 4))) throw new FailedPredicateException(this, "precpred(_ctx, 4)");
						setState(154);
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
						setState(155);
						complex(5);
						}
						break;
					case 3:
						{
						_localctx = new ComplexContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_complex);
						setState(156);
						if (!(precpred(_ctx, 7))) throw new FailedPredicateException(this, "precpred(_ctx, 7)");
						setState(157);
						match(POWER);
						setState(158);
						((ComplexContext)_localctx).n = match(STR);
						setState(159);
						if (!( isNonZero((((ComplexContext)_localctx).n!=null?((ComplexContext)_localctx).n.getText():null)) )) throw new FailedPredicateException(this, " isNonZero($n.text) ");
						}
						break;
					}
					} 
				}
				setState(164);
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
			setState(177);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,16,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(166);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==SUB) {
					{
					setState(165);
					match(SUB);
					}
				}

				setState(168);
				((AngleContext)_localctx).x = match(STR);
				setState(169);
				match(DIV);
				setState(170);
				((AngleContext)_localctx).y = match(STR);
				setState(171);
				if (!( areAllDigits((((AngleContext)_localctx).x!=null?((AngleContext)_localctx).x.getText():null)) && isNonZero((((AngleContext)_localctx).y!=null?((AngleContext)_localctx).y.getText():null)) )) throw new FailedPredicateException(this, " areAllDigits($x.text) && isNonZero($y.text) ");
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(173);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==SUB) {
					{
					setState(172);
					match(SUB);
					}
				}

				setState(175);
				((AngleContext)_localctx).n = match(STR);
				setState(176);
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
			setState(180);
			varcon();
			}
			_ctx.stop = _input.LT(-1);
			setState(187);
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
					setState(182);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(183);
					match(COMMA);
					setState(184);
					varcon();
					}
					} 
				}
				setState(189);
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
		public List<TerminalNode> BAR() { return getTokens(ExtendedDiracParser.BAR); }
		public TerminalNode BAR(int i) {
			return getToken(ExtendedDiracParser.BAR, i);
		}
		public TerminalNode EQ() { return getToken(ExtendedDiracParser.EQ, 0); }
		public List<TerminalNode> STR() { return getTokens(ExtendedDiracParser.STR); }
		public TerminalNode STR(int i) {
			return getToken(ExtendedDiracParser.STR, i);
		}
		public EqContext eq() {
			return getRuleContext(EqContext.class,0);
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
			setState(198);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,18,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(190);
				match(BAR);
				setState(191);
				((VarconContext)_localctx).V = match(STR);
				setState(192);
				match(BAR);
				setState(193);
				match(EQ);
				setState(194);
				((VarconContext)_localctx).N = match(STR);
				setState(195);
				if (!( isALowercaseLetter((((VarconContext)_localctx).V!=null?((VarconContext)_localctx).V.getText():null)) && isNonZero((((VarconContext)_localctx).N!=null?((VarconContext)_localctx).N.getText():null)) )) throw new FailedPredicateException(this, " isALowercaseLetter($V.text) && isNonZero($N.text) ");
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(196);
				eq();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(197);
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
	public static class EqContext extends ParserRuleContext {
		public List<ComplexContext> complex() {
			return getRuleContexts(ComplexContext.class);
		}
		public ComplexContext complex(int i) {
			return getRuleContext(ComplexContext.class,i);
		}
		public TerminalNode EQ() { return getToken(ExtendedDiracParser.EQ, 0); }
		public EqContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_eq; }
	}

	public final EqContext eq() throws RecognitionException {
		EqContext _localctx = new EqContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_eq);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(200);
			complex(0);
			setState(201);
			match(EQ);
			setState(202);
			complex(0);
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
		public List<ComplexContext> complex() {
			return getRuleContexts(ComplexContext.class);
		}
		public ComplexContext complex(int i) {
			return getRuleContext(ComplexContext.class,i);
		}
		public TerminalNode NE() { return getToken(ExtendedDiracParser.NE, 0); }
		public IneqContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_ineq; }
	}

	public final IneqContext ineq() throws RecognitionException {
		IneqContext _localctx = new IneqContext(_ctx, getState());
		enterRule(_localctx, 24, RULE_ineq);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(204);
			complex(0);
			setState(205);
			match(NE);
			setState(206);
			complex(0);
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
	public static class PredicateContext extends ParserRuleContext {
		public EqContext eq() {
			return getRuleContext(EqContext.class,0);
		}
		public IneqContext ineq() {
			return getRuleContext(IneqContext.class,0);
		}
		public List<ComplexContext> complex() {
			return getRuleContexts(ComplexContext.class);
		}
		public ComplexContext complex(int i) {
			return getRuleContext(ComplexContext.class,i);
		}
		public TerminalNode LESS_THAN() { return getToken(ExtendedDiracParser.LESS_THAN, 0); }
		public TerminalNode LESS_EQUAL() { return getToken(ExtendedDiracParser.LESS_EQUAL, 0); }
		public TerminalNode RIGHT_ANGLE_BRACKET() { return getToken(ExtendedDiracParser.RIGHT_ANGLE_BRACKET, 0); }
		public TerminalNode GREATER_EQUAL() { return getToken(ExtendedDiracParser.GREATER_EQUAL, 0); }
		public TerminalNode LOGICAL_NOT() { return getToken(ExtendedDiracParser.LOGICAL_NOT, 0); }
		public List<PredicateContext> predicate() {
			return getRuleContexts(PredicateContext.class);
		}
		public PredicateContext predicate(int i) {
			return getRuleContext(PredicateContext.class,i);
		}
		public TerminalNode LEFT_PARENTHESIS() { return getToken(ExtendedDiracParser.LEFT_PARENTHESIS, 0); }
		public TerminalNode RIGHT_PARENTHESIS() { return getToken(ExtendedDiracParser.RIGHT_PARENTHESIS, 0); }
		public TerminalNode LOGICAL_AND() { return getToken(ExtendedDiracParser.LOGICAL_AND, 0); }
		public TerminalNode LOGICAL_OR() { return getToken(ExtendedDiracParser.LOGICAL_OR, 0); }
		public PredicateContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_predicate; }
	}

	public final PredicateContext predicate() throws RecognitionException {
		return predicate(0);
	}

	private PredicateContext predicate(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		PredicateContext _localctx = new PredicateContext(_ctx, _parentState);
		PredicateContext _prevctx = _localctx;
		int _startState = 26;
		enterRecursionRule(_localctx, 26, RULE_predicate, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(233);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,19,_ctx) ) {
			case 1:
				{
				setState(209);
				eq();
				}
				break;
			case 2:
				{
				setState(210);
				ineq();
				}
				break;
			case 3:
				{
				setState(211);
				complex(0);
				setState(212);
				match(LESS_THAN);
				setState(213);
				complex(0);
				}
				break;
			case 4:
				{
				setState(215);
				complex(0);
				setState(216);
				match(LESS_EQUAL);
				setState(217);
				complex(0);
				}
				break;
			case 5:
				{
				setState(219);
				complex(0);
				setState(220);
				match(RIGHT_ANGLE_BRACKET);
				setState(221);
				complex(0);
				}
				break;
			case 6:
				{
				setState(223);
				complex(0);
				setState(224);
				match(GREATER_EQUAL);
				setState(225);
				complex(0);
				}
				break;
			case 7:
				{
				setState(227);
				match(LOGICAL_NOT);
				setState(228);
				predicate(4);
				}
				break;
			case 8:
				{
				setState(229);
				match(LEFT_PARENTHESIS);
				setState(230);
				predicate(0);
				setState(231);
				match(RIGHT_PARENTHESIS);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(243);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,21,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(241);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,20,_ctx) ) {
					case 1:
						{
						_localctx = new PredicateContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_predicate);
						setState(235);
						if (!(precpred(_ctx, 3))) throw new FailedPredicateException(this, "precpred(_ctx, 3)");
						setState(236);
						match(LOGICAL_AND);
						setState(237);
						predicate(4);
						}
						break;
					case 2:
						{
						_localctx = new PredicateContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_predicate);
						setState(238);
						if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
						setState(239);
						match(LOGICAL_OR);
						setState(240);
						predicate(3);
						}
						break;
					}
					} 
				}
				setState(245);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,21,_ctx);
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
		case 13:
			return predicate_sempred((PredicateContext)_localctx, predIndex);
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
			return  (((ComplexContext)_localctx).func!=null?((ComplexContext)_localctx).func.getText():null) == "real" || (((ComplexContext)_localctx).func!=null?((ComplexContext)_localctx).func.getText():null) == "imag" || (((ComplexContext)_localctx).func!=null?((ComplexContext)_localctx).func.getText():null) == "eipi" || (((ComplexContext)_localctx).func!=null?((ComplexContext)_localctx).func.getText():null) == "ei2pi" ;
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
		}
		return true;
	}
	private boolean predicate_sempred(PredicateContext _localctx, int predIndex) {
		switch (predIndex) {
		case 15:
			return precpred(_ctx, 3);
		case 16:
			return precpred(_ctx, 2);
		}
		return true;
	}

	public static final String _serializedATN =
		"\u0004\u0001\u001e\u00f7\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001"+
		"\u0002\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004"+
		"\u0002\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007"+
		"\u0002\b\u0007\b\u0002\t\u0007\t\u0002\n\u0007\n\u0002\u000b\u0007\u000b"+
		"\u0002\f\u0007\f\u0002\r\u0007\r\u0001\u0000\u0001\u0000\u0001\u0000\u0001"+
		"\u0000\u0001\u0000\u0003\u0000\"\b\u0000\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0003\u0001+\b"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0005\u00010\b\u0001\n\u0001"+
		"\f\u00013\t\u0001\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001"+
		"\u0002\u0001\u0002\u0005\u0002;\b\u0002\n\u0002\f\u0002>\t\u0002\u0001"+
		"\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001"+
		"\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0003\u0003K\b"+
		"\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0005\u0003P\b\u0003\n\u0003"+
		"\f\u0003S\t\u0003\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001"+
		"\u0004\u0001\u0004\u0005\u0004[\b\u0004\n\u0004\f\u0004^\t\u0004\u0001"+
		"\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0005"+
		"\u0005f\b\u0005\n\u0005\f\u0005i\t\u0005\u0001\u0006\u0003\u0006l\b\u0006"+
		"\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0003\u0006r\b\u0006"+
		"\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006"+
		"\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006"+
		"\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0003\u0006"+
		"\u0085\b\u0006\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0003\u0007\u0095\b\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0005\u0007\u00a1\b\u0007\n\u0007"+
		"\f\u0007\u00a4\t\u0007\u0001\b\u0003\b\u00a7\b\b\u0001\b\u0001\b\u0001"+
		"\b\u0001\b\u0001\b\u0003\b\u00ae\b\b\u0001\b\u0001\b\u0003\b\u00b2\b\b"+
		"\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0005\t\u00ba\b\t\n\t"+
		"\f\t\u00bd\t\t\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n"+
		"\u0001\n\u0003\n\u00c7\b\n\u0001\u000b\u0001\u000b\u0001\u000b\u0001\u000b"+
		"\u0001\f\u0001\f\u0001\f\u0001\f\u0001\r\u0001\r\u0001\r\u0001\r\u0001"+
		"\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001"+
		"\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001"+
		"\r\u0001\r\u0001\r\u0003\r\u00ea\b\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001"+
		"\r\u0001\r\u0005\r\u00f2\b\r\n\r\f\r\u00f5\t\r\u0001\r\u0000\b\u0002\u0004"+
		"\u0006\b\n\u000e\u0012\u001a\u000e\u0000\u0002\u0004\u0006\b\n\f\u000e"+
		"\u0010\u0012\u0014\u0016\u0018\u001a\u0000\u0002\u0002\u0000\u0001\u0001"+
		"\u0015\u0015\u0002\u0000\u0005\u0005\t\t\u010a\u0000!\u0001\u0000\u0000"+
		"\u0000\u0002*\u0001\u0000\u0000\u0000\u00044\u0001\u0000\u0000\u0000\u0006"+
		"J\u0001\u0000\u0000\u0000\bT\u0001\u0000\u0000\u0000\n_\u0001\u0000\u0000"+
		"\u0000\f\u0084\u0001\u0000\u0000\u0000\u000e\u0094\u0001\u0000\u0000\u0000"+
		"\u0010\u00b1\u0001\u0000\u0000\u0000\u0012\u00b3\u0001\u0000\u0000\u0000"+
		"\u0014\u00c6\u0001\u0000\u0000\u0000\u0016\u00c8\u0001\u0000\u0000\u0000"+
		"\u0018\u00cc\u0001\u0000\u0000\u0000\u001a\u00e9\u0001\u0000\u0000\u0000"+
		"\u001c\"\u0003\u0002\u0001\u0000\u001d\u001e\u0003\u0002\u0001\u0000\u001e"+
		"\u001f\u0005\u0013\u0000\u0000\u001f \u0003\u0002\u0001\u0000 \"\u0001"+
		"\u0000\u0000\u0000!\u001c\u0001\u0000\u0000\u0000!\u001d\u0001\u0000\u0000"+
		"\u0000\"\u0001\u0001\u0000\u0000\u0000#$\u0006\u0001\uffff\uffff\u0000"+
		"$+\u0003\u0004\u0002\u0000%&\u0003\u0006\u0003\u0000&\'\u0005\f\u0000"+
		"\u0000\'(\u0005\u0014\u0000\u0000()\u0004\u0001\u0000\u0001)+\u0001\u0000"+
		"\u0000\u0000*#\u0001\u0000\u0000\u0000*%\u0001\u0000\u0000\u0000+1\u0001"+
		"\u0000\u0000\u0000,-\n\u0001\u0000\u0000-.\u0005\u000e\u0000\u0000.0\u0003"+
		"\u0002\u0001\u0002/,\u0001\u0000\u0000\u000003\u0001\u0000\u0000\u0000"+
		"1/\u0001\u0000\u0000\u000012\u0001\u0000\u0000\u00002\u0003\u0001\u0000"+
		"\u0000\u000031\u0001\u0000\u0000\u000045\u0006\u0002\uffff\uffff\u0000"+
		"56\u0003\u0006\u0003\u00006<\u0001\u0000\u0000\u000078\n\u0002\u0000\u0000"+
		"89\u0005\u0012\u0000\u00009;\u0003\u0006\u0003\u0000:7\u0001\u0000\u0000"+
		"\u0000;>\u0001\u0000\u0000\u0000<:\u0001\u0000\u0000\u0000<=\u0001\u0000"+
		"\u0000\u0000=\u0005\u0001\u0000\u0000\u0000><\u0001\u0000\u0000\u0000"+
		"?@\u0006\u0003\uffff\uffff\u0000@A\u0005\b\u0000\u0000AB\u0003\b\u0004"+
		"\u0000BC\u0005\u0011\u0000\u0000CK\u0001\u0000\u0000\u0000DE\u0005\b\u0000"+
		"\u0000EF\u0003\b\u0004\u0000FG\u0005\u0004\u0000\u0000GH\u0003\u0012\t"+
		"\u0000HI\u0005\u0011\u0000\u0000IK\u0001\u0000\u0000\u0000J?\u0001\u0000"+
		"\u0000\u0000JD\u0001\u0000\u0000\u0000KQ\u0001\u0000\u0000\u0000LM\n\u0003"+
		"\u0000\u0000MN\u0005\u0017\u0000\u0000NP\u0003\u0006\u0003\u0004OL\u0001"+
		"\u0000\u0000\u0000PS\u0001\u0000\u0000\u0000QO\u0001\u0000\u0000\u0000"+
		"QR\u0001\u0000\u0000\u0000R\u0007\u0001\u0000\u0000\u0000SQ\u0001\u0000"+
		"\u0000\u0000TU\u0006\u0004\uffff\uffff\u0000UV\u0003\n\u0005\u0000V\\"+
		"\u0001\u0000\u0000\u0000WX\n\u0001\u0000\u0000XY\u0005\u0003\u0000\u0000"+
		"Y[\u0003\n\u0005\u0000ZW\u0001\u0000\u0000\u0000[^\u0001\u0000\u0000\u0000"+
		"\\Z\u0001\u0000\u0000\u0000\\]\u0001\u0000\u0000\u0000]\t\u0001\u0000"+
		"\u0000\u0000^\\\u0001\u0000\u0000\u0000_`\u0006\u0005\uffff\uffff\u0000"+
		"`a\u0003\f\u0006\u0000ag\u0001\u0000\u0000\u0000bc\n\u0001\u0000\u0000"+
		"cd\u0007\u0000\u0000\u0000df\u0003\f\u0006\u0000eb\u0001\u0000\u0000\u0000"+
		"fi\u0001\u0000\u0000\u0000ge\u0001\u0000\u0000\u0000gh\u0001\u0000\u0000"+
		"\u0000h\u000b\u0001\u0000\u0000\u0000ig\u0001\u0000\u0000\u0000jl\u0003"+
		"\u000e\u0007\u0000kj\u0001\u0000\u0000\u0000kl\u0001\u0000\u0000\u0000"+
		"lm\u0001\u0000\u0000\u0000mn\u0005\u0002\u0000\u0000no\u0005\u0014\u0000"+
		"\u0000o\u0085\u0005\u000f\u0000\u0000pr\u0003\u000e\u0007\u0000qp\u0001"+
		"\u0000\u0000\u0000qr\u0001\u0000\u0000\u0000rs\u0001\u0000\u0000\u0000"+
		"st\u0005\u0016\u0000\u0000tu\u0003\u0012\t\u0000uv\u0005\u0002\u0000\u0000"+
		"vw\u0005\u0014\u0000\u0000wx\u0005\u000f\u0000\u0000x\u0085\u0001\u0000"+
		"\u0000\u0000yz\u0005\u0015\u0000\u0000z{\u0005\u0002\u0000\u0000{|\u0005"+
		"\u0014\u0000\u0000|\u0085\u0005\u000f\u0000\u0000}~\u0005\u0015\u0000"+
		"\u0000~\u007f\u0005\u0016\u0000\u0000\u007f\u0080\u0003\u0012\t\u0000"+
		"\u0080\u0081\u0005\u0002\u0000\u0000\u0081\u0082\u0005\u0014\u0000\u0000"+
		"\u0082\u0083\u0005\u000f\u0000\u0000\u0083\u0085\u0001\u0000\u0000\u0000"+
		"\u0084k\u0001\u0000\u0000\u0000\u0084q\u0001\u0000\u0000\u0000\u0084y"+
		"\u0001\u0000\u0000\u0000\u0084}\u0001\u0000\u0000\u0000\u0085\r\u0001"+
		"\u0000\u0000\u0000\u0086\u0087\u0006\u0007\uffff\uffff\u0000\u0087\u0088"+
		"\u0005\u0015\u0000\u0000\u0088\u0095\u0003\u000e\u0007\u0006\u0089\u008a"+
		"\u0005\u0007\u0000\u0000\u008a\u008b\u0003\u000e\u0007\u0000\u008b\u008c"+
		"\u0005\u0010\u0000\u0000\u008c\u0095\u0001\u0000\u0000\u0000\u008d\u008e"+
		"\u0005\u0014\u0000\u0000\u008e\u008f\u0005\u0007\u0000\u0000\u008f\u0090"+
		"\u0003\u000e\u0007\u0000\u0090\u0091\u0005\u0010\u0000\u0000\u0091\u0092"+
		"\u0004\u0007\u0006\u0001\u0092\u0095\u0001\u0000\u0000\u0000\u0093\u0095"+
		"\u0005\u0014\u0000\u0000\u0094\u0086\u0001\u0000\u0000\u0000\u0094\u0089"+
		"\u0001\u0000\u0000\u0000\u0094\u008d\u0001\u0000\u0000\u0000\u0094\u0093"+
		"\u0001\u0000\u0000\u0000\u0095\u00a2\u0001\u0000\u0000\u0000\u0096\u0097"+
		"\n\u0005\u0000\u0000\u0097\u0098\u0007\u0001\u0000\u0000\u0098\u00a1\u0003"+
		"\u000e\u0007\u0006\u0099\u009a\n\u0004\u0000\u0000\u009a\u009b\u0007\u0000"+
		"\u0000\u0000\u009b\u00a1\u0003\u000e\u0007\u0005\u009c\u009d\n\u0007\u0000"+
		"\u0000\u009d\u009e\u0005\f\u0000\u0000\u009e\u009f\u0005\u0014\u0000\u0000"+
		"\u009f\u00a1\u0004\u0007\n\u0001\u00a0\u0096\u0001\u0000\u0000\u0000\u00a0"+
		"\u0099\u0001\u0000\u0000\u0000\u00a0\u009c\u0001\u0000\u0000\u0000\u00a1"+
		"\u00a4\u0001\u0000\u0000\u0000\u00a2\u00a0\u0001\u0000\u0000\u0000\u00a2"+
		"\u00a3\u0001\u0000\u0000\u0000\u00a3\u000f\u0001\u0000\u0000\u0000\u00a4"+
		"\u00a2\u0001\u0000\u0000\u0000\u00a5\u00a7\u0005\u0015\u0000\u0000\u00a6"+
		"\u00a5\u0001\u0000\u0000\u0000\u00a6\u00a7\u0001\u0000\u0000\u0000\u00a7"+
		"\u00a8\u0001\u0000\u0000\u0000\u00a8\u00a9\u0005\u0014\u0000\u0000\u00a9"+
		"\u00aa\u0005\u0005\u0000\u0000\u00aa\u00ab\u0005\u0014\u0000\u0000\u00ab"+
		"\u00b2\u0004\b\u000b\u0001\u00ac\u00ae\u0005\u0015\u0000\u0000\u00ad\u00ac"+
		"\u0001\u0000\u0000\u0000\u00ad\u00ae\u0001\u0000\u0000\u0000\u00ae\u00af"+
		"\u0001\u0000\u0000\u0000\u00af\u00b0\u0005\u0014\u0000\u0000\u00b0\u00b2"+
		"\u0004\b\f\u0001\u00b1\u00a6\u0001\u0000\u0000\u0000\u00b1\u00ad\u0001"+
		"\u0000\u0000\u0000\u00b2\u0011\u0001\u0000\u0000\u0000\u00b3\u00b4\u0006"+
		"\t\uffff\uffff\u0000\u00b4\u00b5\u0003\u0014\n\u0000\u00b5\u00bb\u0001"+
		"\u0000\u0000\u0000\u00b6\u00b7\n\u0001\u0000\u0000\u00b7\u00b8\u0005\u0003"+
		"\u0000\u0000\u00b8\u00ba\u0003\u0014\n\u0000\u00b9\u00b6\u0001\u0000\u0000"+
		"\u0000\u00ba\u00bd\u0001\u0000\u0000\u0000\u00bb\u00b9\u0001\u0000\u0000"+
		"\u0000\u00bb\u00bc\u0001\u0000\u0000\u0000\u00bc\u0013\u0001\u0000\u0000"+
		"\u0000\u00bd\u00bb\u0001\u0000\u0000\u0000\u00be\u00bf\u0005\u0002\u0000"+
		"\u0000\u00bf\u00c0\u0005\u0014\u0000\u0000\u00c0\u00c1\u0005\u0002\u0000"+
		"\u0000\u00c1\u00c2\u0005\u0006\u0000\u0000\u00c2\u00c3\u0005\u0014\u0000"+
		"\u0000\u00c3\u00c7\u0004\n\u000e\u0001\u00c4\u00c7\u0003\u0016\u000b\u0000"+
		"\u00c5\u00c7\u0003\u0018\f\u0000\u00c6\u00be\u0001\u0000\u0000\u0000\u00c6"+
		"\u00c4\u0001\u0000\u0000\u0000\u00c6\u00c5\u0001\u0000\u0000\u0000\u00c7"+
		"\u0015\u0001\u0000\u0000\u0000\u00c8\u00c9\u0003\u000e\u0007\u0000\u00c9"+
		"\u00ca\u0005\u0006\u0000\u0000\u00ca\u00cb\u0003\u000e\u0007\u0000\u00cb"+
		"\u0017\u0001\u0000\u0000\u0000\u00cc\u00cd\u0003\u000e\u0007\u0000\u00cd"+
		"\u00ce\u0005\n\u0000\u0000\u00ce\u00cf\u0003\u000e\u0007\u0000\u00cf\u0019"+
		"\u0001\u0000\u0000\u0000\u00d0\u00d1\u0006\r\uffff\uffff\u0000\u00d1\u00ea"+
		"\u0003\u0016\u000b\u0000\u00d2\u00ea\u0003\u0018\f\u0000\u00d3\u00d4\u0003"+
		"\u000e\u0007\u0000\u00d4\u00d5\u0005\u001c\u0000\u0000\u00d5\u00d6\u0003"+
		"\u000e\u0007\u0000\u00d6\u00ea\u0001\u0000\u0000\u0000\u00d7\u00d8\u0003"+
		"\u000e\u0007\u0000\u00d8\u00d9\u0005\u001d\u0000\u0000\u00d9\u00da\u0003"+
		"\u000e\u0007\u0000\u00da\u00ea\u0001\u0000\u0000\u0000\u00db\u00dc\u0003"+
		"\u000e\u0007\u0000\u00dc\u00dd\u0005\u000f\u0000\u0000\u00dd\u00de\u0003"+
		"\u000e\u0007\u0000\u00de\u00ea\u0001\u0000\u0000\u0000\u00df\u00e0\u0003"+
		"\u000e\u0007\u0000\u00e0\u00e1\u0005\u001e\u0000\u0000\u00e1\u00e2\u0003"+
		"\u000e\u0007\u0000\u00e2\u00ea\u0001\u0000\u0000\u0000\u00e3\u00e4\u0005"+
		"\u001b\u0000\u0000\u00e4\u00ea\u0003\u001a\r\u0004\u00e5\u00e6\u0005\u0007"+
		"\u0000\u0000\u00e6\u00e7\u0003\u001a\r\u0000\u00e7\u00e8\u0005\u0010\u0000"+
		"\u0000\u00e8\u00ea\u0001\u0000\u0000\u0000\u00e9\u00d0\u0001\u0000\u0000"+
		"\u0000\u00e9\u00d2\u0001\u0000\u0000\u0000\u00e9\u00d3\u0001\u0000\u0000"+
		"\u0000\u00e9\u00d7\u0001\u0000\u0000\u0000\u00e9\u00db\u0001\u0000\u0000"+
		"\u0000\u00e9\u00df\u0001\u0000\u0000\u0000\u00e9\u00e3\u0001\u0000\u0000"+
		"\u0000\u00e9\u00e5\u0001\u0000\u0000\u0000\u00ea\u00f3\u0001\u0000\u0000"+
		"\u0000\u00eb\u00ec\n\u0003\u0000\u0000\u00ec\u00ed\u0005\u0019\u0000\u0000"+
		"\u00ed\u00f2\u0003\u001a\r\u0004\u00ee\u00ef\n\u0002\u0000\u0000\u00ef"+
		"\u00f0\u0005\u001a\u0000\u0000\u00f0\u00f2\u0003\u001a\r\u0003\u00f1\u00eb"+
		"\u0001\u0000\u0000\u0000\u00f1\u00ee\u0001\u0000\u0000\u0000\u00f2\u00f5"+
		"\u0001\u0000\u0000\u0000\u00f3\u00f1\u0001\u0000\u0000\u0000\u00f3\u00f4"+
		"\u0001\u0000\u0000\u0000\u00f4\u001b\u0001\u0000\u0000\u0000\u00f5\u00f3"+
		"\u0001\u0000\u0000\u0000\u0016!*1<JQ\\gkq\u0084\u0094\u00a0\u00a2\u00a6"+
		"\u00ad\u00b1\u00bb\u00c6\u00e9\u00f1\u00f3";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}