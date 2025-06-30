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
		SEMICOLON=15, STR=16, SUM=17, UNION=18, WS=19;
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
			"'^'", "'''", "'\\u2297'", null, "'}'", "';'", null, null, "'\\u222A'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "ADD", "BAR", "COMMA", "COLON", "EQ", "LEFT_BRACE", "NE", "NEWLINES", 
			"OR", "POWER", "PRIME", "PROD", "RIGHT_ANGLE_BRACKET", "RIGHT_BRACE", 
			"SEMICOLON", "STR", "SUM", "UNION", "WS"
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
		public TsetContext tset() {
			return getRuleContext(TsetContext.class,0);
		}
		public ExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expr; }
	}

	public final ExprContext expr() throws RecognitionException {
		ExprContext _localctx = new ExprContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_expr);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(18);
			tset(0);
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
		public TerminalNode SEMICOLON() { return getToken(ExtendedDiracParser.SEMICOLON, 0); }
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
			setState(31);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,0,_ctx) ) {
			case 1:
				{
				setState(21);
				set(0);
				}
				break;
			case 2:
				{
				setState(22);
				set(0);
				setState(23);
				((TsetContext)_localctx).op = match(POWER);
				setState(24);
				((TsetContext)_localctx).N = match(STR);
				setState(25);
				if (!(isNonZero((((TsetContext)_localctx).N!=null?((TsetContext)_localctx).N.getText():null)))) throw new FailedPredicateException(this, "isNonZero($N.text)");
				}
				break;
			case 3:
				{
				setState(27);
				set(0);
				setState(28);
				((TsetContext)_localctx).op = match(SEMICOLON);
				setState(29);
				set(0);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(38);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,1,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new TsetContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_tset);
					setState(33);
					if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
					setState(34);
					((TsetContext)_localctx).op = match(PROD);
					setState(35);
					tset(3);
					}
					} 
				}
				setState(40);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,1,_ctx);
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
			setState(52);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,2,_ctx) ) {
			case 1:
				{
				setState(42);
				match(LEFT_BRACE);
				setState(43);
				diracs(0);
				setState(44);
				match(RIGHT_BRACE);
				}
				break;
			case 2:
				{
				setState(46);
				match(LEFT_BRACE);
				setState(47);
				diracs(0);
				setState(48);
				match(COLON);
				setState(49);
				varcons(0);
				setState(50);
				match(RIGHT_BRACE);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(59);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,3,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new SetContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_set);
					setState(54);
					if (!(precpred(_ctx, 3))) throw new FailedPredicateException(this, "precpred(_ctx, 3)");
					setState(55);
					((SetContext)_localctx).op = match(UNION);
					setState(56);
					set(4);
					}
					} 
				}
				setState(61);
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
			setState(63);
			dirac(0);
			}
			_ctx.stop = _input.LT(-1);
			setState(70);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,4,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new DiracsContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_diracs);
					setState(65);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(66);
					match(COMMA);
					setState(67);
					dirac(0);
					}
					} 
				}
				setState(72);
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
			setState(74);
			term();
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
					_localctx = new DiracContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_dirac);
					setState(76);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(77);
					((DiracContext)_localctx).op = match(ADD);
					setState(78);
					term();
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
			setState(95);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,6,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(84);
				((TermContext)_localctx).C = match(STR);
				setState(85);
				match(BAR);
				setState(86);
				((TermContext)_localctx).VStr = match(STR);
				setState(87);
				match(RIGHT_ANGLE_BRACKET);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(88);
				((TermContext)_localctx).C = match(STR);
				setState(89);
				match(SUM);
				setState(90);
				varcons(0);
				setState(91);
				match(BAR);
				setState(92);
				((TermContext)_localctx).VStr = match(STR);
				setState(93);
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
			setState(98);
			varcon();
			}
			_ctx.stop = _input.LT(-1);
			setState(105);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,7,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new VarconsContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_varcons);
					setState(100);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(101);
					match(COMMA);
					setState(102);
					varcon();
					}
					} 
				}
				setState(107);
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
			setState(119);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,8,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(108);
				match(BAR);
				setState(109);
				((VarconContext)_localctx).V = match(STR);
				setState(110);
				match(BAR);
				setState(111);
				match(EQ);
				setState(112);
				((VarconContext)_localctx).N = match(STR);
				setState(113);
				if (!(isALowercaseLetter((((VarconContext)_localctx).V!=null?((VarconContext)_localctx).V.getText():null)) && isNonZero((((VarconContext)_localctx).N!=null?((VarconContext)_localctx).N.getText():null)))) throw new FailedPredicateException(this, "isALowercaseLetter($V.text) && isNonZero($N.text)");
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(114);
				((VarconContext)_localctx).V = match(STR);
				setState(115);
				match(EQ);
				setState(116);
				((VarconContext)_localctx).CStr = match(STR);
				setState(117);
				if (!(isALowercaseLetter((((VarconContext)_localctx).V!=null?((VarconContext)_localctx).V.getText():null)) && isAConstantBinaryString((((VarconContext)_localctx).CStr!=null?((VarconContext)_localctx).CStr.getText():null)))) throw new FailedPredicateException(this, "isALowercaseLetter($V.text) && isAConstantBinaryString($CStr.text)");
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(118);
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
			setState(121);
			((IneqContext)_localctx).L = match(STR);
			setState(122);
			match(NE);
			setState(123);
			((IneqContext)_localctx).R = match(STR);
			setState(124);
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
			return precpred(_ctx, 2);
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
		"\u0004\u0001\u0013\u007f\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001"+
		"\u0002\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004"+
		"\u0002\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007"+
		"\u0002\b\u0007\b\u0001\u0000\u0001\u0000\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0003\u0001 \b\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0005\u0001%\b\u0001\n\u0001\f\u0001(\t\u0001\u0001"+
		"\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001"+
		"\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0003\u00025\b"+
		"\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0005\u0002:\b\u0002\n\u0002"+
		"\f\u0002=\t\u0002\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001"+
		"\u0003\u0001\u0003\u0005\u0003E\b\u0003\n\u0003\f\u0003H\t\u0003\u0001"+
		"\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0005"+
		"\u0004P\b\u0004\n\u0004\f\u0004S\t\u0004\u0001\u0005\u0001\u0005\u0001"+
		"\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001"+
		"\u0005\u0001\u0005\u0001\u0005\u0003\u0005`\b\u0005\u0001\u0006\u0001"+
		"\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0005\u0006h\b"+
		"\u0006\n\u0006\f\u0006k\t\u0006\u0001\u0007\u0001\u0007\u0001\u0007\u0001"+
		"\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001"+
		"\u0007\u0001\u0007\u0003\u0007x\b\u0007\u0001\b\u0001\b\u0001\b\u0001"+
		"\b\u0001\b\u0001\b\u0000\u0005\u0002\u0004\u0006\b\f\t\u0000\u0002\u0004"+
		"\u0006\b\n\f\u000e\u0010\u0000\u0000\u0080\u0000\u0012\u0001\u0000\u0000"+
		"\u0000\u0002\u001f\u0001\u0000\u0000\u0000\u00044\u0001\u0000\u0000\u0000"+
		"\u0006>\u0001\u0000\u0000\u0000\bI\u0001\u0000\u0000\u0000\n_\u0001\u0000"+
		"\u0000\u0000\fa\u0001\u0000\u0000\u0000\u000ew\u0001\u0000\u0000\u0000"+
		"\u0010y\u0001\u0000\u0000\u0000\u0012\u0013\u0003\u0002\u0001\u0000\u0013"+
		"\u0001\u0001\u0000\u0000\u0000\u0014\u0015\u0006\u0001\uffff\uffff\u0000"+
		"\u0015 \u0003\u0004\u0002\u0000\u0016\u0017\u0003\u0004\u0002\u0000\u0017"+
		"\u0018\u0005\n\u0000\u0000\u0018\u0019\u0005\u0010\u0000\u0000\u0019\u001a"+
		"\u0004\u0001\u0000\u0001\u001a \u0001\u0000\u0000\u0000\u001b\u001c\u0003"+
		"\u0004\u0002\u0000\u001c\u001d\u0005\u000f\u0000\u0000\u001d\u001e\u0003"+
		"\u0004\u0002\u0000\u001e \u0001\u0000\u0000\u0000\u001f\u0014\u0001\u0000"+
		"\u0000\u0000\u001f\u0016\u0001\u0000\u0000\u0000\u001f\u001b\u0001\u0000"+
		"\u0000\u0000 &\u0001\u0000\u0000\u0000!\"\n\u0002\u0000\u0000\"#\u0005"+
		"\f\u0000\u0000#%\u0003\u0002\u0001\u0003$!\u0001\u0000\u0000\u0000%(\u0001"+
		"\u0000\u0000\u0000&$\u0001\u0000\u0000\u0000&\'\u0001\u0000\u0000\u0000"+
		"\'\u0003\u0001\u0000\u0000\u0000(&\u0001\u0000\u0000\u0000)*\u0006\u0002"+
		"\uffff\uffff\u0000*+\u0005\u0006\u0000\u0000+,\u0003\u0006\u0003\u0000"+
		",-\u0005\u000e\u0000\u0000-5\u0001\u0000\u0000\u0000./\u0005\u0006\u0000"+
		"\u0000/0\u0003\u0006\u0003\u000001\u0005\u0004\u0000\u000012\u0003\f\u0006"+
		"\u000023\u0005\u000e\u0000\u000035\u0001\u0000\u0000\u00004)\u0001\u0000"+
		"\u0000\u00004.\u0001\u0000\u0000\u00005;\u0001\u0000\u0000\u000067\n\u0003"+
		"\u0000\u000078\u0005\u0012\u0000\u00008:\u0003\u0004\u0002\u000496\u0001"+
		"\u0000\u0000\u0000:=\u0001\u0000\u0000\u0000;9\u0001\u0000\u0000\u0000"+
		";<\u0001\u0000\u0000\u0000<\u0005\u0001\u0000\u0000\u0000=;\u0001\u0000"+
		"\u0000\u0000>?\u0006\u0003\uffff\uffff\u0000?@\u0003\b\u0004\u0000@F\u0001"+
		"\u0000\u0000\u0000AB\n\u0001\u0000\u0000BC\u0005\u0003\u0000\u0000CE\u0003"+
		"\b\u0004\u0000DA\u0001\u0000\u0000\u0000EH\u0001\u0000\u0000\u0000FD\u0001"+
		"\u0000\u0000\u0000FG\u0001\u0000\u0000\u0000G\u0007\u0001\u0000\u0000"+
		"\u0000HF\u0001\u0000\u0000\u0000IJ\u0006\u0004\uffff\uffff\u0000JK\u0003"+
		"\n\u0005\u0000KQ\u0001\u0000\u0000\u0000LM\n\u0001\u0000\u0000MN\u0005"+
		"\u0001\u0000\u0000NP\u0003\n\u0005\u0000OL\u0001\u0000\u0000\u0000PS\u0001"+
		"\u0000\u0000\u0000QO\u0001\u0000\u0000\u0000QR\u0001\u0000\u0000\u0000"+
		"R\t\u0001\u0000\u0000\u0000SQ\u0001\u0000\u0000\u0000TU\u0005\u0010\u0000"+
		"\u0000UV\u0005\u0002\u0000\u0000VW\u0005\u0010\u0000\u0000W`\u0005\r\u0000"+
		"\u0000XY\u0005\u0010\u0000\u0000YZ\u0005\u0011\u0000\u0000Z[\u0003\f\u0006"+
		"\u0000[\\\u0005\u0002\u0000\u0000\\]\u0005\u0010\u0000\u0000]^\u0005\r"+
		"\u0000\u0000^`\u0001\u0000\u0000\u0000_T\u0001\u0000\u0000\u0000_X\u0001"+
		"\u0000\u0000\u0000`\u000b\u0001\u0000\u0000\u0000ab\u0006\u0006\uffff"+
		"\uffff\u0000bc\u0003\u000e\u0007\u0000ci\u0001\u0000\u0000\u0000de\n\u0001"+
		"\u0000\u0000ef\u0005\u0003\u0000\u0000fh\u0003\u000e\u0007\u0000gd\u0001"+
		"\u0000\u0000\u0000hk\u0001\u0000\u0000\u0000ig\u0001\u0000\u0000\u0000"+
		"ij\u0001\u0000\u0000\u0000j\r\u0001\u0000\u0000\u0000ki\u0001\u0000\u0000"+
		"\u0000lm\u0005\u0002\u0000\u0000mn\u0005\u0010\u0000\u0000no\u0005\u0002"+
		"\u0000\u0000op\u0005\u0005\u0000\u0000pq\u0005\u0010\u0000\u0000qx\u0004"+
		"\u0007\u0006\u0001rs\u0005\u0010\u0000\u0000st\u0005\u0005\u0000\u0000"+
		"tu\u0005\u0010\u0000\u0000ux\u0004\u0007\u0007\u0001vx\u0003\u0010\b\u0000"+
		"wl\u0001\u0000\u0000\u0000wr\u0001\u0000\u0000\u0000wv\u0001\u0000\u0000"+
		"\u0000x\u000f\u0001\u0000\u0000\u0000yz\u0005\u0010\u0000\u0000z{\u0005"+
		"\u0007\u0000\u0000{|\u0005\u0010\u0000\u0000|}\u0004\b\b\u0001}\u0011"+
		"\u0001\u0000\u0000\u0000\t\u001f&4;FQ_iw";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}