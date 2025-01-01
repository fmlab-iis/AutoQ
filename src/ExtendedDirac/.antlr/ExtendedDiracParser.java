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
		KET=10, LEFT_BRACKET=11, LEFT_CURLY_BRACKET=12, MUL=13, NEWLINES=14, POWER=15, 
		PROD=16, RIGHT_BRACKET=17, RIGHT_CURLY_BRACKET=18, SUB=19, SETMINUS=20, 
		SQRT2=21, UNION=22, WHERE=23, WS=24, NAME=25;
	public static final int
		RULE_extendedDirac = 0, RULE_muloperators = 1, RULE_muloperator = 2, RULE_accepted = 3, 
		RULE_set = 4, RULE_diracs = 5, RULE_dirac = 6, RULE_cket = 7, RULE_complex = 8, 
		RULE_angle = 9, RULE_ijklens = 10, RULE_ijklen = 11;
	private static String[] makeRuleNames() {
		return new String[] {
			"extendedDirac", "muloperators", "muloperator", "accepted", "set", "diracs", 
			"dirac", "cket", "complex", "angle", "ijklens", "ijklen"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'+'", "'|'", "','", "'/'", null, "'ei2pi'", "'eipi'", "'='", "'\\u2229'", 
			null, "'('", "'{'", "'*'", null, "'^'", "'\\u2297'", "')'", "'}'", "'-'", 
			"'\\'", "'sqrt2'", "'\\u222A'", "'where'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "ADD", "BAR", "COMMA", "DIV", "DIGITS", "EI2PI", "EIPI", "EQ", 
			"INTERSECTION", "KET", "LEFT_BRACKET", "LEFT_CURLY_BRACKET", "MUL", "NEWLINES", 
			"POWER", "PROD", "RIGHT_BRACKET", "RIGHT_CURLY_BRACKET", "SUB", "SETMINUS", 
			"SQRT2", "UNION", "WHERE", "WS", "NAME"
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
		public AcceptedContext accepted() {
			return getRuleContext(AcceptedContext.class,0);
		}
		public TerminalNode EOF() { return getToken(ExtendedDiracParser.EOF, 0); }
		public TerminalNode WHERE() { return getToken(ExtendedDiracParser.WHERE, 0); }
		public TerminalNode NEWLINES() { return getToken(ExtendedDiracParser.NEWLINES, 0); }
		public MuloperatorsContext muloperators() {
			return getRuleContext(MuloperatorsContext.class,0);
		}
		public ExtendedDiracContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_extendedDirac; }
	}

	public final ExtendedDiracContext extendedDirac() throws RecognitionException {
		ExtendedDiracContext _localctx = new ExtendedDiracContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_extendedDirac);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(24);
			accepted();
			setState(28);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==WHERE) {
				{
				setState(25);
				match(WHERE);
				setState(26);
				match(NEWLINES);
				setState(27);
				muloperators();
				}
			}

			setState(30);
			match(EOF);
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
	public static class MuloperatorsContext extends ParserRuleContext {
		public List<MuloperatorContext> muloperator() {
			return getRuleContexts(MuloperatorContext.class);
		}
		public MuloperatorContext muloperator(int i) {
			return getRuleContext(MuloperatorContext.class,i);
		}
		public MuloperatorsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_muloperators; }
	}

	public final MuloperatorsContext muloperators() throws RecognitionException {
		MuloperatorsContext _localctx = new MuloperatorsContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_muloperators);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(33); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(32);
				muloperator();
				}
				}
				setState(35); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( (((_la) & ~0x3f) == 0 && ((1L << _la) & 36178144L) != 0) );
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
	public static class MuloperatorContext extends ParserRuleContext {
		public List<ComplexContext> complex() {
			return getRuleContexts(ComplexContext.class);
		}
		public ComplexContext complex(int i) {
			return getRuleContext(ComplexContext.class,i);
		}
		public TerminalNode PROD() { return getToken(ExtendedDiracParser.PROD, 0); }
		public TerminalNode EQ() { return getToken(ExtendedDiracParser.EQ, 0); }
		public TerminalNode NEWLINES() { return getToken(ExtendedDiracParser.NEWLINES, 0); }
		public TerminalNode EOF() { return getToken(ExtendedDiracParser.EOF, 0); }
		public MuloperatorContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_muloperator; }
	}

	public final MuloperatorContext muloperator() throws RecognitionException {
		MuloperatorContext _localctx = new MuloperatorContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_muloperator);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(37);
			complex(0);
			setState(38);
			match(PROD);
			setState(39);
			complex(0);
			setState(40);
			match(EQ);
			setState(41);
			complex(0);
			setState(42);
			_la = _input.LA(1);
			if ( !(_la==EOF || _la==NEWLINES) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
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
	public static class AcceptedContext extends ParserRuleContext {
		public List<SetContext> set() {
			return getRuleContexts(SetContext.class);
		}
		public SetContext set(int i) {
			return getRuleContext(SetContext.class,i);
		}
		public TerminalNode SETMINUS() { return getToken(ExtendedDiracParser.SETMINUS, 0); }
		public AcceptedContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_accepted; }
	}

	public final AcceptedContext accepted() throws RecognitionException {
		AcceptedContext _localctx = new AcceptedContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_accepted);
		try {
			setState(49);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,2,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(44);
				set(0);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(45);
				set(0);
				setState(46);
				match(SETMINUS);
				setState(47);
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
		int _startState = 8;
		enterRecursionRule(_localctx, 8, RULE_set, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(66);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,3,_ctx) ) {
			case 1:
				{
				setState(52);
				match(LEFT_BRACKET);
				setState(53);
				set(0);
				setState(54);
				match(RIGHT_BRACKET);
				}
				break;
			case 2:
				{
				setState(56);
				match(LEFT_CURLY_BRACKET);
				setState(57);
				diracs(0);
				setState(58);
				match(RIGHT_CURLY_BRACKET);
				}
				break;
			case 3:
				{
				setState(60);
				match(LEFT_CURLY_BRACKET);
				setState(61);
				dirac(0);
				setState(62);
				match(BAR);
				setState(63);
				ijklens(0);
				setState(64);
				match(RIGHT_CURLY_BRACKET);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(80);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,5,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(78);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,4,_ctx) ) {
					case 1:
						{
						_localctx = new SetContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_set);
						setState(68);
						if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
						setState(69);
						((SetContext)_localctx).op = match(PROD);
						setState(70);
						set(3);
						}
						break;
					case 2:
						{
						_localctx = new SetContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_set);
						setState(71);
						if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
						setState(72);
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
						setState(73);
						set(2);
						}
						break;
					case 3:
						{
						_localctx = new SetContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_set);
						setState(74);
						if (!(precpred(_ctx, 6))) throw new FailedPredicateException(this, "precpred(_ctx, 6)");
						setState(75);
						match(POWER);
						setState(76);
						((SetContext)_localctx).n = match(DIGITS);
						setState(77);
						if (!(isNonZero((((SetContext)_localctx).n!=null?((SetContext)_localctx).n.getText():null)))) throw new FailedPredicateException(this, "isNonZero($n.text)");
						}
						break;
					}
					} 
				}
				setState(82);
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
		int _startState = 10;
		enterRecursionRule(_localctx, 10, RULE_diracs, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(84);
			dirac(0);
			}
			_ctx.stop = _input.LT(-1);
			setState(91);
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
					setState(86);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(87);
					match(COMMA);
					setState(88);
					dirac(0);
					}
					} 
				}
				setState(93);
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
		int _startState = 12;
		enterRecursionRule(_localctx, 12, RULE_dirac, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(95);
			cket();
			}
			_ctx.stop = _input.LT(-1);
			setState(102);
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
					setState(97);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(98);
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
					setState(99);
					cket();
					}
					} 
				}
				setState(104);
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
		enterRule(_localctx, 14, RULE_cket);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(110);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,8,_ctx) ) {
			case 1:
				{
				setState(105);
				complex(0);
				}
				break;
			case 2:
				{
				setState(106);
				complex(0);
				setState(107);
				((CketContext)_localctx).op = match(MUL);
				}
				break;
			case 3:
				{
				setState(109);
				match(SUB);
				}
				break;
			}
			setState(112);
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
		int _startState = 16;
		enterRecursionRule(_localctx, 16, RULE_complex, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(136);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case LEFT_BRACKET:
				{
				setState(116);
				match(LEFT_BRACKET);
				setState(117);
				complex(0);
				setState(118);
				match(RIGHT_BRACKET);
				}
				break;
			case SUB:
				{
				setState(120);
				match(SUB);
				setState(121);
				complex(6);
				}
				break;
			case EI2PI:
				{
				setState(122);
				match(EI2PI);
				setState(123);
				match(LEFT_BRACKET);
				setState(124);
				angle();
				setState(125);
				match(RIGHT_BRACKET);
				}
				break;
			case EIPI:
				{
				setState(127);
				match(EIPI);
				setState(128);
				match(LEFT_BRACKET);
				setState(129);
				angle();
				setState(130);
				match(RIGHT_BRACKET);
				}
				break;
			case DIGITS:
				{
				setState(132);
				match(DIGITS);
				}
				break;
			case SQRT2:
				{
				setState(133);
				match(SQRT2);
				}
				break;
			case NAME:
				{
				setState(134);
				((ComplexContext)_localctx).var = match(NAME);
				 if (!predefinedVars.contains((((ComplexContext)_localctx).var!=null?((ComplexContext)_localctx).var.getText():null))) isSymbolicAutomaton = true; 
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			_ctx.stop = _input.LT(-1);
			setState(152);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,12,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(150);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,11,_ctx) ) {
					case 1:
						{
						_localctx = new ComplexContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_complex);
						setState(138);
						if (!(precpred(_ctx, 9))) throw new FailedPredicateException(this, "precpred(_ctx, 9)");
						setState(140);
						_errHandler.sync(this);
						_la = _input.LA(1);
						if (_la==DIV || _la==MUL) {
							{
							setState(139);
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

						setState(142);
						complex(10);
						}
						break;
					case 2:
						{
						_localctx = new ComplexContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_complex);
						setState(143);
						if (!(precpred(_ctx, 8))) throw new FailedPredicateException(this, "precpred(_ctx, 8)");
						setState(144);
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
						setState(145);
						complex(9);
						}
						break;
					case 3:
						{
						_localctx = new ComplexContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_complex);
						setState(146);
						if (!(precpred(_ctx, 10))) throw new FailedPredicateException(this, "precpred(_ctx, 10)");
						setState(147);
						match(POWER);
						setState(148);
						((ComplexContext)_localctx).n = match(DIGITS);
						setState(149);
						if (!(isNonZero((((ComplexContext)_localctx).n!=null?((ComplexContext)_localctx).n.getText():null)))) throw new FailedPredicateException(this, "isNonZero($n.text)");
						}
						break;
					}
					} 
				}
				setState(154);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,12,_ctx);
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
		enterRule(_localctx, 18, RULE_angle);
		int _la;
		try {
			setState(166);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,15,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(156);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==SUB) {
					{
					setState(155);
					match(SUB);
					}
				}

				setState(158);
				((AngleContext)_localctx).x = match(DIGITS);
				setState(159);
				match(DIV);
				setState(160);
				((AngleContext)_localctx).y = match(DIGITS);
				setState(161);
				if (!(isNonZero((((AngleContext)_localctx).y!=null?((AngleContext)_localctx).y.getText():null)))) throw new FailedPredicateException(this, "isNonZero($y.text)");
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(163);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==SUB) {
					{
					setState(162);
					match(SUB);
					}
				}

				setState(165);
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
		int _startState = 20;
		enterRecursionRule(_localctx, 20, RULE_ijklens, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(169);
			ijklen();
			}
			_ctx.stop = _input.LT(-1);
			setState(176);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,16,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new IjklensContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_ijklens);
					setState(171);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(172);
					match(COMMA);
					setState(173);
					ijklen();
					}
					} 
				}
				setState(178);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,16,_ctx);
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
		enterRule(_localctx, 22, RULE_ijklen);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(179);
			match(BAR);
			setState(180);
			((IjklenContext)_localctx).var = match(NAME);
			setState(181);
			match(BAR);
			setState(182);
			match(EQ);
			setState(183);
			((IjklenContext)_localctx).len = match(DIGITS);
			setState(184);
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
		case 4:
			return set_sempred((SetContext)_localctx, predIndex);
		case 5:
			return diracs_sempred((DiracsContext)_localctx, predIndex);
		case 6:
			return dirac_sempred((DiracContext)_localctx, predIndex);
		case 8:
			return complex_sempred((ComplexContext)_localctx, predIndex);
		case 9:
			return angle_sempred((AngleContext)_localctx, predIndex);
		case 10:
			return ijklens_sempred((IjklensContext)_localctx, predIndex);
		case 11:
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
		"\u0004\u0001\u0019\u00bb\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001"+
		"\u0002\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004"+
		"\u0002\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007"+
		"\u0002\b\u0007\b\u0002\t\u0007\t\u0002\n\u0007\n\u0002\u000b\u0007\u000b"+
		"\u0001\u0000\u0001\u0000\u0001\u0000\u0001\u0000\u0003\u0000\u001d\b\u0000"+
		"\u0001\u0000\u0001\u0000\u0001\u0001\u0004\u0001\"\b\u0001\u000b\u0001"+
		"\f\u0001#\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002"+
		"\u0001\u0002\u0001\u0002\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003"+
		"\u0001\u0003\u0003\u00032\b\u0003\u0001\u0004\u0001\u0004\u0001\u0004"+
		"\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004"+
		"\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004"+
		"\u0003\u0004C\b\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004"+
		"\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004"+
		"\u0005\u0004O\b\u0004\n\u0004\f\u0004R\t\u0004\u0001\u0005\u0001\u0005"+
		"\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0005\u0005Z\b\u0005"+
		"\n\u0005\f\u0005]\t\u0005\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006"+
		"\u0001\u0006\u0001\u0006\u0005\u0006e\b\u0006\n\u0006\f\u0006h\t\u0006"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0003\u0007"+
		"o\b\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\b\u0001\b\u0001\b"+
		"\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001"+
		"\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001"+
		"\b\u0003\b\u0089\b\b\u0001\b\u0001\b\u0003\b\u008d\b\b\u0001\b\u0001\b"+
		"\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0005\b\u0097\b\b\n\b"+
		"\f\b\u009a\t\b\u0001\t\u0003\t\u009d\b\t\u0001\t\u0001\t\u0001\t\u0001"+
		"\t\u0001\t\u0003\t\u00a4\b\t\u0001\t\u0003\t\u00a7\b\t\u0001\n\u0001\n"+
		"\u0001\n\u0001\n\u0001\n\u0001\n\u0005\n\u00af\b\n\n\n\f\n\u00b2\t\n\u0001"+
		"\u000b\u0001\u000b\u0001\u000b\u0001\u000b\u0001\u000b\u0001\u000b\u0001"+
		"\u000b\u0001\u000b\u0000\u0005\b\n\f\u0010\u0014\f\u0000\u0002\u0004\u0006"+
		"\b\n\f\u000e\u0010\u0012\u0014\u0016\u0000\u0004\u0001\u0001\u000e\u000e"+
		"\u0002\u0000\t\t\u0016\u0016\u0002\u0000\u0001\u0001\u0013\u0013\u0002"+
		"\u0000\u0004\u0004\r\r\u00c9\u0000\u0018\u0001\u0000\u0000\u0000\u0002"+
		"!\u0001\u0000\u0000\u0000\u0004%\u0001\u0000\u0000\u0000\u00061\u0001"+
		"\u0000\u0000\u0000\bB\u0001\u0000\u0000\u0000\nS\u0001\u0000\u0000\u0000"+
		"\f^\u0001\u0000\u0000\u0000\u000en\u0001\u0000\u0000\u0000\u0010\u0088"+
		"\u0001\u0000\u0000\u0000\u0012\u00a6\u0001\u0000\u0000\u0000\u0014\u00a8"+
		"\u0001\u0000\u0000\u0000\u0016\u00b3\u0001\u0000\u0000\u0000\u0018\u001c"+
		"\u0003\u0006\u0003\u0000\u0019\u001a\u0005\u0017\u0000\u0000\u001a\u001b"+
		"\u0005\u000e\u0000\u0000\u001b\u001d\u0003\u0002\u0001\u0000\u001c\u0019"+
		"\u0001\u0000\u0000\u0000\u001c\u001d\u0001\u0000\u0000\u0000\u001d\u001e"+
		"\u0001\u0000\u0000\u0000\u001e\u001f\u0005\u0000\u0000\u0001\u001f\u0001"+
		"\u0001\u0000\u0000\u0000 \"\u0003\u0004\u0002\u0000! \u0001\u0000\u0000"+
		"\u0000\"#\u0001\u0000\u0000\u0000#!\u0001\u0000\u0000\u0000#$\u0001\u0000"+
		"\u0000\u0000$\u0003\u0001\u0000\u0000\u0000%&\u0003\u0010\b\u0000&\'\u0005"+
		"\u0010\u0000\u0000\'(\u0003\u0010\b\u0000()\u0005\b\u0000\u0000)*\u0003"+
		"\u0010\b\u0000*+\u0007\u0000\u0000\u0000+\u0005\u0001\u0000\u0000\u0000"+
		",2\u0003\b\u0004\u0000-.\u0003\b\u0004\u0000./\u0005\u0014\u0000\u0000"+
		"/0\u0003\b\u0004\u000002\u0001\u0000\u0000\u00001,\u0001\u0000\u0000\u0000"+
		"1-\u0001\u0000\u0000\u00002\u0007\u0001\u0000\u0000\u000034\u0006\u0004"+
		"\uffff\uffff\u000045\u0005\u000b\u0000\u000056\u0003\b\u0004\u000067\u0005"+
		"\u0011\u0000\u00007C\u0001\u0000\u0000\u000089\u0005\f\u0000\u00009:\u0003"+
		"\n\u0005\u0000:;\u0005\u0012\u0000\u0000;C\u0001\u0000\u0000\u0000<=\u0005"+
		"\f\u0000\u0000=>\u0003\f\u0006\u0000>?\u0005\u0002\u0000\u0000?@\u0003"+
		"\u0014\n\u0000@A\u0005\u0012\u0000\u0000AC\u0001\u0000\u0000\u0000B3\u0001"+
		"\u0000\u0000\u0000B8\u0001\u0000\u0000\u0000B<\u0001\u0000\u0000\u0000"+
		"CP\u0001\u0000\u0000\u0000DE\n\u0002\u0000\u0000EF\u0005\u0010\u0000\u0000"+
		"FO\u0003\b\u0004\u0003GH\n\u0001\u0000\u0000HI\u0007\u0001\u0000\u0000"+
		"IO\u0003\b\u0004\u0002JK\n\u0006\u0000\u0000KL\u0005\u000f\u0000\u0000"+
		"LM\u0005\u0005\u0000\u0000MO\u0004\u0004\u0003\u0001ND\u0001\u0000\u0000"+
		"\u0000NG\u0001\u0000\u0000\u0000NJ\u0001\u0000\u0000\u0000OR\u0001\u0000"+
		"\u0000\u0000PN\u0001\u0000\u0000\u0000PQ\u0001\u0000\u0000\u0000Q\t\u0001"+
		"\u0000\u0000\u0000RP\u0001\u0000\u0000\u0000ST\u0006\u0005\uffff\uffff"+
		"\u0000TU\u0003\f\u0006\u0000U[\u0001\u0000\u0000\u0000VW\n\u0001\u0000"+
		"\u0000WX\u0005\u0003\u0000\u0000XZ\u0003\f\u0006\u0000YV\u0001\u0000\u0000"+
		"\u0000Z]\u0001\u0000\u0000\u0000[Y\u0001\u0000\u0000\u0000[\\\u0001\u0000"+
		"\u0000\u0000\\\u000b\u0001\u0000\u0000\u0000][\u0001\u0000\u0000\u0000"+
		"^_\u0006\u0006\uffff\uffff\u0000_`\u0003\u000e\u0007\u0000`f\u0001\u0000"+
		"\u0000\u0000ab\n\u0001\u0000\u0000bc\u0007\u0002\u0000\u0000ce\u0003\u000e"+
		"\u0007\u0000da\u0001\u0000\u0000\u0000eh\u0001\u0000\u0000\u0000fd\u0001"+
		"\u0000\u0000\u0000fg\u0001\u0000\u0000\u0000g\r\u0001\u0000\u0000\u0000"+
		"hf\u0001\u0000\u0000\u0000io\u0003\u0010\b\u0000jk\u0003\u0010\b\u0000"+
		"kl\u0005\r\u0000\u0000lo\u0001\u0000\u0000\u0000mo\u0005\u0013\u0000\u0000"+
		"ni\u0001\u0000\u0000\u0000nj\u0001\u0000\u0000\u0000nm\u0001\u0000\u0000"+
		"\u0000no\u0001\u0000\u0000\u0000op\u0001\u0000\u0000\u0000pq\u0005\n\u0000"+
		"\u0000qr\u0006\u0007\uffff\uffff\u0000r\u000f\u0001\u0000\u0000\u0000"+
		"st\u0006\b\uffff\uffff\u0000tu\u0005\u000b\u0000\u0000uv\u0003\u0010\b"+
		"\u0000vw\u0005\u0011\u0000\u0000w\u0089\u0001\u0000\u0000\u0000xy\u0005"+
		"\u0013\u0000\u0000y\u0089\u0003\u0010\b\u0006z{\u0005\u0006\u0000\u0000"+
		"{|\u0005\u000b\u0000\u0000|}\u0003\u0012\t\u0000}~\u0005\u0011\u0000\u0000"+
		"~\u0089\u0001\u0000\u0000\u0000\u007f\u0080\u0005\u0007\u0000\u0000\u0080"+
		"\u0081\u0005\u000b\u0000\u0000\u0081\u0082\u0003\u0012\t\u0000\u0082\u0083"+
		"\u0005\u0011\u0000\u0000\u0083\u0089\u0001\u0000\u0000\u0000\u0084\u0089"+
		"\u0005\u0005\u0000\u0000\u0085\u0089\u0005\u0015\u0000\u0000\u0086\u0087"+
		"\u0005\u0019\u0000\u0000\u0087\u0089\u0006\b\uffff\uffff\u0000\u0088s"+
		"\u0001\u0000\u0000\u0000\u0088x\u0001\u0000\u0000\u0000\u0088z\u0001\u0000"+
		"\u0000\u0000\u0088\u007f\u0001\u0000\u0000\u0000\u0088\u0084\u0001\u0000"+
		"\u0000\u0000\u0088\u0085\u0001\u0000\u0000\u0000\u0088\u0086\u0001\u0000"+
		"\u0000\u0000\u0089\u0098\u0001\u0000\u0000\u0000\u008a\u008c\n\t\u0000"+
		"\u0000\u008b\u008d\u0007\u0003\u0000\u0000\u008c\u008b\u0001\u0000\u0000"+
		"\u0000\u008c\u008d\u0001\u0000\u0000\u0000\u008d\u008e\u0001\u0000\u0000"+
		"\u0000\u008e\u0097\u0003\u0010\b\n\u008f\u0090\n\b\u0000\u0000\u0090\u0091"+
		"\u0007\u0002\u0000\u0000\u0091\u0097\u0003\u0010\b\t\u0092\u0093\n\n\u0000"+
		"\u0000\u0093\u0094\u0005\u000f\u0000\u0000\u0094\u0095\u0005\u0005\u0000"+
		"\u0000\u0095\u0097\u0004\b\t\u0001\u0096\u008a\u0001\u0000\u0000\u0000"+
		"\u0096\u008f\u0001\u0000\u0000\u0000\u0096\u0092\u0001\u0000\u0000\u0000"+
		"\u0097\u009a\u0001\u0000\u0000\u0000\u0098\u0096\u0001\u0000\u0000\u0000"+
		"\u0098\u0099\u0001\u0000\u0000\u0000\u0099\u0011\u0001\u0000\u0000\u0000"+
		"\u009a\u0098\u0001\u0000\u0000\u0000\u009b\u009d\u0005\u0013\u0000\u0000"+
		"\u009c\u009b\u0001\u0000\u0000\u0000\u009c\u009d\u0001\u0000\u0000\u0000"+
		"\u009d\u009e\u0001\u0000\u0000\u0000\u009e\u009f\u0005\u0005\u0000\u0000"+
		"\u009f\u00a0\u0005\u0004\u0000\u0000\u00a0\u00a1\u0005\u0005\u0000\u0000"+
		"\u00a1\u00a7\u0004\t\n\u0001\u00a2\u00a4\u0005\u0013\u0000\u0000\u00a3"+
		"\u00a2\u0001\u0000\u0000\u0000\u00a3\u00a4\u0001\u0000\u0000\u0000\u00a4"+
		"\u00a5\u0001\u0000\u0000\u0000\u00a5\u00a7\u0005\u0005\u0000\u0000\u00a6"+
		"\u009c\u0001\u0000\u0000\u0000\u00a6\u00a3\u0001\u0000\u0000\u0000\u00a7"+
		"\u0013\u0001\u0000\u0000\u0000\u00a8\u00a9\u0006\n\uffff\uffff\u0000\u00a9"+
		"\u00aa\u0003\u0016\u000b\u0000\u00aa\u00b0\u0001\u0000\u0000\u0000\u00ab"+
		"\u00ac\n\u0001\u0000\u0000\u00ac\u00ad\u0005\u0003\u0000\u0000\u00ad\u00af"+
		"\u0003\u0016\u000b\u0000\u00ae\u00ab\u0001\u0000\u0000\u0000\u00af\u00b2"+
		"\u0001\u0000\u0000\u0000\u00b0\u00ae\u0001\u0000\u0000\u0000\u00b0\u00b1"+
		"\u0001\u0000\u0000\u0000\u00b1\u0015\u0001\u0000\u0000\u0000\u00b2\u00b0"+
		"\u0001\u0000\u0000\u0000\u00b3\u00b4\u0005\u0002\u0000\u0000\u00b4\u00b5"+
		"\u0005\u0019\u0000\u0000\u00b5\u00b6\u0005\u0002\u0000\u0000\u00b6\u00b7"+
		"\u0005\b\u0000\u0000\u00b7\u00b8\u0005\u0005\u0000\u0000\u00b8\u00b9\u0004"+
		"\u000b\f\u0001\u00b9\u0017\u0001\u0000\u0000\u0000\u0011\u001c#1BNP[f"+
		"n\u0088\u008c\u0096\u0098\u009c\u00a3\u00a6\u00b0";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}