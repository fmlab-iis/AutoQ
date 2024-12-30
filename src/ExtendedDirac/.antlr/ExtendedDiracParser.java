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
		ADD=1, BAR=2, COMMA=3, DIV=4, DIGITS=5, EI2PI=6, EIPI=7, EQ=8, INTERSECTION=9, 
		KET=10, LEFT_BRACKET=11, LEFT_CURLY_BRACKET=12, MUL=13, NAME=14, POWER=15, 
		PROD=16, RIGHT_BRACKET=17, RIGHT_CURLY_BRACKET=18, SUB=19, SETMINUS=20, 
		SQRT2=21, UNION=22, WS=23;
	public static final int
		RULE_extendedDirac = 0, RULE_set = 1, RULE_diracs = 2, RULE_dirac = 3, 
		RULE_cket = 4, RULE_complex = 5, RULE_angle = 6, RULE_ijklens = 7, RULE_ijklen = 8;
	private static String[] makeRuleNames() {
		return new String[] {
			"extendedDirac", "set", "diracs", "dirac", "cket", "complex", "angle", 
			"ijklens", "ijklen"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'+'", "'|'", "','", "'/'", null, "'ei2pi'", "'eipi'", "'='", "'\\u2229'", 
			null, "'('", "'{'", "'*'", null, "'^'", "'\\u2297'", "')'", "'}'", "'-'", 
			"'\\'", "'sqrt2'", "'\\u222A'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "ADD", "BAR", "COMMA", "DIV", "DIGITS", "EI2PI", "EIPI", "EQ", 
			"INTERSECTION", "KET", "LEFT_BRACKET", "LEFT_CURLY_BRACKET", "MUL", "NAME", 
			"POWER", "PROD", "RIGHT_BRACKET", "RIGHT_CURLY_BRACKET", "SUB", "SETMINUS", 
			"SQRT2", "UNION", "WS"
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
	    bool isASingleLetter(const std::string& text) {
	        return text.length() == 1 && 'a' <= text.at(0) && text.at(0) <= 'z';
	    }

	public ExtendedDiracParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ExtendedDiracContext extends ParserRuleContext {
		public List<SetContext> set() {
			return getRuleContexts(SetContext.class);
		}
		public SetContext set(int i) {
			return getRuleContext(SetContext.class,i);
		}
		public TerminalNode SETMINUS() { return getToken(ExtendedDiracParser.SETMINUS, 0); }
		public ExtendedDiracContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_extendedDirac; }
	}

	public final ExtendedDiracContext extendedDirac() throws RecognitionException {
		ExtendedDiracContext _localctx = new ExtendedDiracContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_extendedDirac);
		try {
			setState(23);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,0,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(18);
				set(0);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(19);
				set(0);
				setState(20);
				match(SETMINUS);
				setState(21);
				set(0);
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
	public static class SetContext extends ParserRuleContext {
		public Token op;
		public Token n;
		public TerminalNode LEFT_BRACKET() { return getToken(ExtendedDiracParser.LEFT_BRACKET, 0); }
		public List<SetContext> set() {
			return getRuleContexts(SetContext.class);
		}
		public SetContext set(int i) {
			return getRuleContext(SetContext.class,i);
		}
		public TerminalNode RIGHT_BRACKET() { return getToken(ExtendedDiracParser.RIGHT_BRACKET, 0); }
		public TerminalNode LEFT_CURLY_BRACKET() { return getToken(ExtendedDiracParser.LEFT_CURLY_BRACKET, 0); }
		public DiracsContext diracs() {
			return getRuleContext(DiracsContext.class,0);
		}
		public TerminalNode RIGHT_CURLY_BRACKET() { return getToken(ExtendedDiracParser.RIGHT_CURLY_BRACKET, 0); }
		public DiracContext dirac() {
			return getRuleContext(DiracContext.class,0);
		}
		public TerminalNode BAR() { return getToken(ExtendedDiracParser.BAR, 0); }
		public IjklensContext ijklens() {
			return getRuleContext(IjklensContext.class,0);
		}
		public TerminalNode PROD() { return getToken(ExtendedDiracParser.PROD, 0); }
		public TerminalNode UNION() { return getToken(ExtendedDiracParser.UNION, 0); }
		public TerminalNode INTERSECTION() { return getToken(ExtendedDiracParser.INTERSECTION, 0); }
		public TerminalNode POWER() { return getToken(ExtendedDiracParser.POWER, 0); }
		public TerminalNode DIGITS() { return getToken(ExtendedDiracParser.DIGITS, 0); }
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
		int _startState = 2;
		enterRecursionRule(_localctx, 2, RULE_set, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(40);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,1,_ctx) ) {
			case 1:
				{
				setState(26);
				match(LEFT_BRACKET);
				setState(27);
				set(0);
				setState(28);
				match(RIGHT_BRACKET);
				}
				break;
			case 2:
				{
				setState(30);
				match(LEFT_CURLY_BRACKET);
				setState(31);
				diracs(0);
				setState(32);
				match(RIGHT_CURLY_BRACKET);
				}
				break;
			case 3:
				{
				setState(34);
				match(LEFT_CURLY_BRACKET);
				setState(35);
				dirac(0);
				setState(36);
				match(BAR);
				setState(37);
				ijklens(0);
				setState(38);
				match(RIGHT_CURLY_BRACKET);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(54);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,3,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(52);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,2,_ctx) ) {
					case 1:
						{
						_localctx = new SetContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_set);
						setState(42);
						if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
						setState(43);
						((SetContext)_localctx).op = match(PROD);
						setState(44);
						set(3);
						}
						break;
					case 2:
						{
						_localctx = new SetContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_set);
						setState(45);
						if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
						setState(46);
						((SetContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==INTERSECTION || _la==UNION) ) {
							((SetContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(47);
						set(2);
						}
						break;
					case 3:
						{
						_localctx = new SetContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_set);
						setState(48);
						if (!(precpred(_ctx, 6))) throw new FailedPredicateException(this, "precpred(_ctx, 6)");
						setState(49);
						match(POWER);
						setState(50);
						((SetContext)_localctx).n = match(DIGITS);
						setState(51);
						if (!(isNonZero((((SetContext)_localctx).n!=null?((SetContext)_localctx).n.getText():null)))) throw new FailedPredicateException(this, "isNonZero($n.text)");
						}
						break;
					}
					} 
				}
				setState(56);
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
		int _startState = 4;
		enterRecursionRule(_localctx, 4, RULE_diracs, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(58);
			dirac(0);
			}
			_ctx.stop = _input.LT(-1);
			setState(65);
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
					setState(60);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(61);
					match(COMMA);
					setState(62);
					dirac(0);
					}
					} 
				}
				setState(67);
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
		public CketContext cket() {
			return getRuleContext(CketContext.class,0);
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
		int _startState = 6;
		enterRecursionRule(_localctx, 6, RULE_dirac, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(69);
			cket();
			}
			_ctx.stop = _input.LT(-1);
			setState(76);
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
					setState(71);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(72);
					((DiracContext)_localctx).op = _input.LT(1);
					_la = _input.LA(1);
					if ( !(_la==ADD || _la==SUB) ) {
						((DiracContext)_localctx).op = (Token)_errHandler.recoverInline(this);
					}
					else {
						if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
						_errHandler.reportMatch(this);
						consume();
					}
					setState(73);
					cket();
					}
					} 
				}
				setState(78);
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
	public static class CketContext extends ParserRuleContext {
		public Token op;
		public Token KET;
		public TerminalNode KET() { return getToken(ExtendedDiracParser.KET, 0); }
		public ComplexContext complex() {
			return getRuleContext(ComplexContext.class,0);
		}
		public TerminalNode SUB() { return getToken(ExtendedDiracParser.SUB, 0); }
		public TerminalNode MUL() { return getToken(ExtendedDiracParser.MUL, 0); }
		public CketContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_cket; }
	}

	public final CketContext cket() throws RecognitionException {
		CketContext _localctx = new CketContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_cket);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(84);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,6,_ctx) ) {
			case 1:
				{
				setState(79);
				complex(0);
				}
				break;
			case 2:
				{
				setState(80);
				complex(0);
				setState(81);
				((CketContext)_localctx).op = match(MUL);
				}
				break;
			case 3:
				{
				setState(83);
				match(SUB);
				}
				break;
			}
			setState(86);
			((CketContext)_localctx).KET = match(KET);

			        std::string text = (((CketContext)_localctx).KET!=null?((CketContext)_localctx).KET.getText():null);           // Get the full text of the KET token
			        std::string state = text.substr(1, text.length() - 2); // Remove the first and last characters
			    
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
		public Token var;
		public Token op;
		public Token n;
		public TerminalNode LEFT_BRACKET() { return getToken(ExtendedDiracParser.LEFT_BRACKET, 0); }
		public List<ComplexContext> complex() {
			return getRuleContexts(ComplexContext.class);
		}
		public ComplexContext complex(int i) {
			return getRuleContext(ComplexContext.class,i);
		}
		public TerminalNode RIGHT_BRACKET() { return getToken(ExtendedDiracParser.RIGHT_BRACKET, 0); }
		public TerminalNode SUB() { return getToken(ExtendedDiracParser.SUB, 0); }
		public TerminalNode EI2PI() { return getToken(ExtendedDiracParser.EI2PI, 0); }
		public AngleContext angle() {
			return getRuleContext(AngleContext.class,0);
		}
		public TerminalNode EIPI() { return getToken(ExtendedDiracParser.EIPI, 0); }
		public TerminalNode DIGITS() { return getToken(ExtendedDiracParser.DIGITS, 0); }
		public TerminalNode SQRT2() { return getToken(ExtendedDiracParser.SQRT2, 0); }
		public TerminalNode NAME() { return getToken(ExtendedDiracParser.NAME, 0); }
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
		int _startState = 10;
		enterRecursionRule(_localctx, 10, RULE_complex, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(110);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case LEFT_BRACKET:
				{
				setState(90);
				match(LEFT_BRACKET);
				setState(91);
				complex(0);
				setState(92);
				match(RIGHT_BRACKET);
				}
				break;
			case SUB:
				{
				setState(94);
				match(SUB);
				setState(95);
				complex(6);
				}
				break;
			case EI2PI:
				{
				setState(96);
				match(EI2PI);
				setState(97);
				match(LEFT_BRACKET);
				setState(98);
				angle();
				setState(99);
				match(RIGHT_BRACKET);
				}
				break;
			case EIPI:
				{
				setState(101);
				match(EIPI);
				setState(102);
				match(LEFT_BRACKET);
				setState(103);
				angle();
				setState(104);
				match(RIGHT_BRACKET);
				}
				break;
			case DIGITS:
				{
				setState(106);
				match(DIGITS);
				}
				break;
			case SQRT2:
				{
				setState(107);
				match(SQRT2);
				}
				break;
			case NAME:
				{
				setState(108);
				((ComplexContext)_localctx).var = match(NAME);
				 if (!predefinedVars.contains((((ComplexContext)_localctx).var!=null?((ComplexContext)_localctx).var.getText():null))) isSymbolicAutomaton = true; 
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			_ctx.stop = _input.LT(-1);
			setState(126);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,10,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(124);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,9,_ctx) ) {
					case 1:
						{
						_localctx = new ComplexContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_complex);
						setState(112);
						if (!(precpred(_ctx, 9))) throw new FailedPredicateException(this, "precpred(_ctx, 9)");
						setState(114);
						_errHandler.sync(this);
						_la = _input.LA(1);
						if (_la==DIV || _la==MUL) {
							{
							setState(113);
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
							}
						}

						setState(116);
						complex(10);
						}
						break;
					case 2:
						{
						_localctx = new ComplexContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_complex);
						setState(117);
						if (!(precpred(_ctx, 8))) throw new FailedPredicateException(this, "precpred(_ctx, 8)");
						setState(118);
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
						setState(119);
						complex(9);
						}
						break;
					case 3:
						{
						_localctx = new ComplexContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_complex);
						setState(120);
						if (!(precpred(_ctx, 10))) throw new FailedPredicateException(this, "precpred(_ctx, 10)");
						setState(121);
						match(POWER);
						setState(122);
						((ComplexContext)_localctx).n = match(DIGITS);
						setState(123);
						if (!(isNonZero((((ComplexContext)_localctx).n!=null?((ComplexContext)_localctx).n.getText():null)))) throw new FailedPredicateException(this, "isNonZero($n.text)");
						}
						break;
					}
					} 
				}
				setState(128);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,10,_ctx);
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
		public List<TerminalNode> DIGITS() { return getTokens(ExtendedDiracParser.DIGITS); }
		public TerminalNode DIGITS(int i) {
			return getToken(ExtendedDiracParser.DIGITS, i);
		}
		public TerminalNode SUB() { return getToken(ExtendedDiracParser.SUB, 0); }
		public AngleContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_angle; }
	}

	public final AngleContext angle() throws RecognitionException {
		AngleContext _localctx = new AngleContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_angle);
		int _la;
		try {
			setState(140);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,13,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(130);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==SUB) {
					{
					setState(129);
					match(SUB);
					}
				}

				setState(132);
				((AngleContext)_localctx).x = match(DIGITS);
				setState(133);
				match(DIV);
				setState(134);
				((AngleContext)_localctx).y = match(DIGITS);
				setState(135);
				if (!(isNonZero((((AngleContext)_localctx).y!=null?((AngleContext)_localctx).y.getText():null)))) throw new FailedPredicateException(this, "isNonZero($y.text)");
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(137);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==SUB) {
					{
					setState(136);
					match(SUB);
					}
				}

				setState(139);
				((AngleContext)_localctx).n = match(DIGITS);
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
	public static class IjklensContext extends ParserRuleContext {
		public IjklenContext ijklen() {
			return getRuleContext(IjklenContext.class,0);
		}
		public IjklensContext ijklens() {
			return getRuleContext(IjklensContext.class,0);
		}
		public TerminalNode COMMA() { return getToken(ExtendedDiracParser.COMMA, 0); }
		public IjklensContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_ijklens; }
	}

	public final IjklensContext ijklens() throws RecognitionException {
		return ijklens(0);
	}

	private IjklensContext ijklens(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		IjklensContext _localctx = new IjklensContext(_ctx, _parentState);
		IjklensContext _prevctx = _localctx;
		int _startState = 14;
		enterRecursionRule(_localctx, 14, RULE_ijklens, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(143);
			ijklen();
			}
			_ctx.stop = _input.LT(-1);
			setState(150);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,14,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new IjklensContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_ijklens);
					setState(145);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(146);
					match(COMMA);
					setState(147);
					ijklen();
					}
					} 
				}
				setState(152);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,14,_ctx);
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
	public static class IjklenContext extends ParserRuleContext {
		public Token var;
		public Token len;
		public List<TerminalNode> BAR() { return getTokens(ExtendedDiracParser.BAR); }
		public TerminalNode BAR(int i) {
			return getToken(ExtendedDiracParser.BAR, i);
		}
		public TerminalNode EQ() { return getToken(ExtendedDiracParser.EQ, 0); }
		public TerminalNode NAME() { return getToken(ExtendedDiracParser.NAME, 0); }
		public TerminalNode DIGITS() { return getToken(ExtendedDiracParser.DIGITS, 0); }
		public IjklenContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_ijklen; }
	}

	public final IjklenContext ijklen() throws RecognitionException {
		IjklenContext _localctx = new IjklenContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_ijklen);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(153);
			match(BAR);
			setState(154);
			((IjklenContext)_localctx).var = match(NAME);
			setState(155);
			match(BAR);
			setState(156);
			match(EQ);
			setState(157);
			((IjklenContext)_localctx).len = match(DIGITS);
			setState(158);
			if (!(isASingleLetter((((IjklenContext)_localctx).var!=null?((IjklenContext)_localctx).var.getText():null)) && isNonZero((((IjklenContext)_localctx).len!=null?((IjklenContext)_localctx).len.getText():null)))) throw new FailedPredicateException(this, "isASingleLetter($var.text) && isNonZero($len.text)");
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
			return set_sempred((SetContext)_localctx, predIndex);
		case 2:
			return diracs_sempred((DiracsContext)_localctx, predIndex);
		case 3:
			return dirac_sempred((DiracContext)_localctx, predIndex);
		case 5:
			return complex_sempred((ComplexContext)_localctx, predIndex);
		case 6:
			return angle_sempred((AngleContext)_localctx, predIndex);
		case 7:
			return ijklens_sempred((IjklensContext)_localctx, predIndex);
		case 8:
			return ijklen_sempred((IjklenContext)_localctx, predIndex);
		}
		return true;
	}
	private boolean set_sempred(SetContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return precpred(_ctx, 2);
		case 1:
			return precpred(_ctx, 1);
		case 2:
			return precpred(_ctx, 6);
		case 3:
			return isNonZero((((SetContext)_localctx).n!=null?((SetContext)_localctx).n.getText():null));
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
			return precpred(_ctx, 9);
		case 7:
			return precpred(_ctx, 8);
		case 8:
			return precpred(_ctx, 10);
		case 9:
			return isNonZero((((ComplexContext)_localctx).n!=null?((ComplexContext)_localctx).n.getText():null));
		}
		return true;
	}
	private boolean angle_sempred(AngleContext _localctx, int predIndex) {
		switch (predIndex) {
		case 10:
			return isNonZero((((AngleContext)_localctx).y!=null?((AngleContext)_localctx).y.getText():null));
		}
		return true;
	}
	private boolean ijklens_sempred(IjklensContext _localctx, int predIndex) {
		switch (predIndex) {
		case 11:
			return precpred(_ctx, 1);
		}
		return true;
	}
	private boolean ijklen_sempred(IjklenContext _localctx, int predIndex) {
		switch (predIndex) {
		case 12:
			return isASingleLetter((((IjklenContext)_localctx).var!=null?((IjklenContext)_localctx).var.getText():null)) && isNonZero((((IjklenContext)_localctx).len!=null?((IjklenContext)_localctx).len.getText():null));
		}
		return true;
	}

	public static final String _serializedATN =
		"\u0004\u0001\u0017\u00a1\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001"+
		"\u0002\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004"+
		"\u0002\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007"+
		"\u0002\b\u0007\b\u0001\u0000\u0001\u0000\u0001\u0000\u0001\u0000\u0001"+
		"\u0000\u0003\u0000\u0018\b\u0000\u0001\u0001\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0003"+
		"\u0001)\b\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0005"+
		"\u00015\b\u0001\n\u0001\f\u00018\t\u0001\u0001\u0002\u0001\u0002\u0001"+
		"\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0005\u0002@\b\u0002\n\u0002"+
		"\f\u0002C\t\u0002\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001"+
		"\u0003\u0001\u0003\u0005\u0003K\b\u0003\n\u0003\f\u0003N\t\u0003\u0001"+
		"\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0003\u0004U\b"+
		"\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0005\u0001\u0005\u0001"+
		"\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001"+
		"\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001"+
		"\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001"+
		"\u0005\u0003\u0005o\b\u0005\u0001\u0005\u0001\u0005\u0003\u0005s\b\u0005"+
		"\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005"+
		"\u0001\u0005\u0001\u0005\u0005\u0005}\b\u0005\n\u0005\f\u0005\u0080\t"+
		"\u0005\u0001\u0006\u0003\u0006\u0083\b\u0006\u0001\u0006\u0001\u0006\u0001"+
		"\u0006\u0001\u0006\u0001\u0006\u0003\u0006\u008a\b\u0006\u0001\u0006\u0003"+
		"\u0006\u008d\b\u0006\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001"+
		"\u0007\u0001\u0007\u0005\u0007\u0095\b\u0007\n\u0007\f\u0007\u0098\t\u0007"+
		"\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0000"+
		"\u0005\u0002\u0004\u0006\n\u000e\t\u0000\u0002\u0004\u0006\b\n\f\u000e"+
		"\u0010\u0000\u0003\u0002\u0000\t\t\u0016\u0016\u0002\u0000\u0001\u0001"+
		"\u0013\u0013\u0002\u0000\u0004\u0004\r\r\u00b0\u0000\u0017\u0001\u0000"+
		"\u0000\u0000\u0002(\u0001\u0000\u0000\u0000\u00049\u0001\u0000\u0000\u0000"+
		"\u0006D\u0001\u0000\u0000\u0000\bT\u0001\u0000\u0000\u0000\nn\u0001\u0000"+
		"\u0000\u0000\f\u008c\u0001\u0000\u0000\u0000\u000e\u008e\u0001\u0000\u0000"+
		"\u0000\u0010\u0099\u0001\u0000\u0000\u0000\u0012\u0018\u0003\u0002\u0001"+
		"\u0000\u0013\u0014\u0003\u0002\u0001\u0000\u0014\u0015\u0005\u0014\u0000"+
		"\u0000\u0015\u0016\u0003\u0002\u0001\u0000\u0016\u0018\u0001\u0000\u0000"+
		"\u0000\u0017\u0012\u0001\u0000\u0000\u0000\u0017\u0013\u0001\u0000\u0000"+
		"\u0000\u0018\u0001\u0001\u0000\u0000\u0000\u0019\u001a\u0006\u0001\uffff"+
		"\uffff\u0000\u001a\u001b\u0005\u000b\u0000\u0000\u001b\u001c\u0003\u0002"+
		"\u0001\u0000\u001c\u001d\u0005\u0011\u0000\u0000\u001d)\u0001\u0000\u0000"+
		"\u0000\u001e\u001f\u0005\f\u0000\u0000\u001f \u0003\u0004\u0002\u0000"+
		" !\u0005\u0012\u0000\u0000!)\u0001\u0000\u0000\u0000\"#\u0005\f\u0000"+
		"\u0000#$\u0003\u0006\u0003\u0000$%\u0005\u0002\u0000\u0000%&\u0003\u000e"+
		"\u0007\u0000&\'\u0005\u0012\u0000\u0000\')\u0001\u0000\u0000\u0000(\u0019"+
		"\u0001\u0000\u0000\u0000(\u001e\u0001\u0000\u0000\u0000(\"\u0001\u0000"+
		"\u0000\u0000)6\u0001\u0000\u0000\u0000*+\n\u0002\u0000\u0000+,\u0005\u0010"+
		"\u0000\u0000,5\u0003\u0002\u0001\u0003-.\n\u0001\u0000\u0000./\u0007\u0000"+
		"\u0000\u0000/5\u0003\u0002\u0001\u000201\n\u0006\u0000\u000012\u0005\u000f"+
		"\u0000\u000023\u0005\u0005\u0000\u000035\u0004\u0001\u0003\u00014*\u0001"+
		"\u0000\u0000\u00004-\u0001\u0000\u0000\u000040\u0001\u0000\u0000\u0000"+
		"58\u0001\u0000\u0000\u000064\u0001\u0000\u0000\u000067\u0001\u0000\u0000"+
		"\u00007\u0003\u0001\u0000\u0000\u000086\u0001\u0000\u0000\u00009:\u0006"+
		"\u0002\uffff\uffff\u0000:;\u0003\u0006\u0003\u0000;A\u0001\u0000\u0000"+
		"\u0000<=\n\u0001\u0000\u0000=>\u0005\u0003\u0000\u0000>@\u0003\u0006\u0003"+
		"\u0000?<\u0001\u0000\u0000\u0000@C\u0001\u0000\u0000\u0000A?\u0001\u0000"+
		"\u0000\u0000AB\u0001\u0000\u0000\u0000B\u0005\u0001\u0000\u0000\u0000"+
		"CA\u0001\u0000\u0000\u0000DE\u0006\u0003\uffff\uffff\u0000EF\u0003\b\u0004"+
		"\u0000FL\u0001\u0000\u0000\u0000GH\n\u0001\u0000\u0000HI\u0007\u0001\u0000"+
		"\u0000IK\u0003\b\u0004\u0000JG\u0001\u0000\u0000\u0000KN\u0001\u0000\u0000"+
		"\u0000LJ\u0001\u0000\u0000\u0000LM\u0001\u0000\u0000\u0000M\u0007\u0001"+
		"\u0000\u0000\u0000NL\u0001\u0000\u0000\u0000OU\u0003\n\u0005\u0000PQ\u0003"+
		"\n\u0005\u0000QR\u0005\r\u0000\u0000RU\u0001\u0000\u0000\u0000SU\u0005"+
		"\u0013\u0000\u0000TO\u0001\u0000\u0000\u0000TP\u0001\u0000\u0000\u0000"+
		"TS\u0001\u0000\u0000\u0000TU\u0001\u0000\u0000\u0000UV\u0001\u0000\u0000"+
		"\u0000VW\u0005\n\u0000\u0000WX\u0006\u0004\uffff\uffff\u0000X\t\u0001"+
		"\u0000\u0000\u0000YZ\u0006\u0005\uffff\uffff\u0000Z[\u0005\u000b\u0000"+
		"\u0000[\\\u0003\n\u0005\u0000\\]\u0005\u0011\u0000\u0000]o\u0001\u0000"+
		"\u0000\u0000^_\u0005\u0013\u0000\u0000_o\u0003\n\u0005\u0006`a\u0005\u0006"+
		"\u0000\u0000ab\u0005\u000b\u0000\u0000bc\u0003\f\u0006\u0000cd\u0005\u0011"+
		"\u0000\u0000do\u0001\u0000\u0000\u0000ef\u0005\u0007\u0000\u0000fg\u0005"+
		"\u000b\u0000\u0000gh\u0003\f\u0006\u0000hi\u0005\u0011\u0000\u0000io\u0001"+
		"\u0000\u0000\u0000jo\u0005\u0005\u0000\u0000ko\u0005\u0015\u0000\u0000"+
		"lm\u0005\u000e\u0000\u0000mo\u0006\u0005\uffff\uffff\u0000nY\u0001\u0000"+
		"\u0000\u0000n^\u0001\u0000\u0000\u0000n`\u0001\u0000\u0000\u0000ne\u0001"+
		"\u0000\u0000\u0000nj\u0001\u0000\u0000\u0000nk\u0001\u0000\u0000\u0000"+
		"nl\u0001\u0000\u0000\u0000o~\u0001\u0000\u0000\u0000pr\n\t\u0000\u0000"+
		"qs\u0007\u0002\u0000\u0000rq\u0001\u0000\u0000\u0000rs\u0001\u0000\u0000"+
		"\u0000st\u0001\u0000\u0000\u0000t}\u0003\n\u0005\nuv\n\b\u0000\u0000v"+
		"w\u0007\u0001\u0000\u0000w}\u0003\n\u0005\txy\n\n\u0000\u0000yz\u0005"+
		"\u000f\u0000\u0000z{\u0005\u0005\u0000\u0000{}\u0004\u0005\t\u0001|p\u0001"+
		"\u0000\u0000\u0000|u\u0001\u0000\u0000\u0000|x\u0001\u0000\u0000\u0000"+
		"}\u0080\u0001\u0000\u0000\u0000~|\u0001\u0000\u0000\u0000~\u007f\u0001"+
		"\u0000\u0000\u0000\u007f\u000b\u0001\u0000\u0000\u0000\u0080~\u0001\u0000"+
		"\u0000\u0000\u0081\u0083\u0005\u0013\u0000\u0000\u0082\u0081\u0001\u0000"+
		"\u0000\u0000\u0082\u0083\u0001\u0000\u0000\u0000\u0083\u0084\u0001\u0000"+
		"\u0000\u0000\u0084\u0085\u0005\u0005\u0000\u0000\u0085\u0086\u0005\u0004"+
		"\u0000\u0000\u0086\u0087\u0005\u0005\u0000\u0000\u0087\u008d\u0004\u0006"+
		"\n\u0001\u0088\u008a\u0005\u0013\u0000\u0000\u0089\u0088\u0001\u0000\u0000"+
		"\u0000\u0089\u008a\u0001\u0000\u0000\u0000\u008a\u008b\u0001\u0000\u0000"+
		"\u0000\u008b\u008d\u0005\u0005\u0000\u0000\u008c\u0082\u0001\u0000\u0000"+
		"\u0000\u008c\u0089\u0001\u0000\u0000\u0000\u008d\r\u0001\u0000\u0000\u0000"+
		"\u008e\u008f\u0006\u0007\uffff\uffff\u0000\u008f\u0090\u0003\u0010\b\u0000"+
		"\u0090\u0096\u0001\u0000\u0000\u0000\u0091\u0092\n\u0001\u0000\u0000\u0092"+
		"\u0093\u0005\u0003\u0000\u0000\u0093\u0095\u0003\u0010\b\u0000\u0094\u0091"+
		"\u0001\u0000\u0000\u0000\u0095\u0098\u0001\u0000\u0000\u0000\u0096\u0094"+
		"\u0001\u0000\u0000\u0000\u0096\u0097\u0001\u0000\u0000\u0000\u0097\u000f"+
		"\u0001\u0000\u0000\u0000\u0098\u0096\u0001\u0000\u0000\u0000\u0099\u009a"+
		"\u0005\u0002\u0000\u0000\u009a\u009b\u0005\u000e\u0000\u0000\u009b\u009c"+
		"\u0005\u0002\u0000\u0000\u009c\u009d\u0005\b\u0000\u0000\u009d\u009e\u0005"+
		"\u0005\u0000\u0000\u009e\u009f\u0004\b\f\u0001\u009f\u0011\u0001\u0000"+
		"\u0000\u0000\u000f\u0017(46ALTnr|~\u0082\u0089\u008c\u0096";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}