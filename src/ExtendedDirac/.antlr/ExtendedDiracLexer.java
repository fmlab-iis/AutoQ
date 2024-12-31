// Generated from /home/alan23273850/AutoQ/src/ExtendedDirac/ExtendedDiracLexer.g4 by ANTLR 4.13.1
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast", "CheckReturnValue", "this-escape"})
public class ExtendedDiracLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.13.1", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		ADD=1, BAR=2, COMMA=3, DIV=4, DIGITS=5, EI2PI=6, EIPI=7, EQ=8, INTERSECTION=9, 
		KET=10, LEFT_BRACKET=11, LEFT_CURLY_BRACKET=12, MUL=13, NEWLINES=14, POWER=15, 
		PROD=16, RIGHT_BRACKET=17, RIGHT_CURLY_BRACKET=18, SUB=19, SETMINUS=20, 
		SQRT2=21, UNION=22, WHERE=23, WS=24, NAME=25;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"ADD", "BAR", "COMMA", "DIV", "DIGITS", "EI2PI", "EIPI", "EQ", "INTERSECTION", 
			"KET", "LEFT_BRACKET", "LEFT_CURLY_BRACKET", "MUL", "NEWLINES", "POWER", 
			"PROD", "RIGHT_BRACKET", "RIGHT_CURLY_BRACKET", "SUB", "SETMINUS", "SQRT2", 
			"UNION", "WHERE", "WS", "NAME"
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


	    bool skipNewline = true;


	public ExtendedDiracLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "ExtendedDiracLexer.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getChannelNames() { return channelNames; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	@Override
	public void action(RuleContext _localctx, int ruleIndex, int actionIndex) {
		switch (ruleIndex) {
		case 13:
			NEWLINES_action((RuleContext)_localctx, actionIndex);
			break;
		case 22:
			WHERE_action((RuleContext)_localctx, actionIndex);
			break;
		}
	}
	private void NEWLINES_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 0:
			 if (skipNewline) skip(); 
			break;
		}
	}
	private void WHERE_action(RuleContext _localctx, int actionIndex) {
		switch (actionIndex) {
		case 1:
			 skipNewline = false; 
			break;
		}
	}

	public static final String _serializedATN =
		"\u0004\u0000\u0019\u008e\u0006\uffff\uffff\u0002\u0000\u0007\u0000\u0002"+
		"\u0001\u0007\u0001\u0002\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002"+
		"\u0004\u0007\u0004\u0002\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002"+
		"\u0007\u0007\u0007\u0002\b\u0007\b\u0002\t\u0007\t\u0002\n\u0007\n\u0002"+
		"\u000b\u0007\u000b\u0002\f\u0007\f\u0002\r\u0007\r\u0002\u000e\u0007\u000e"+
		"\u0002\u000f\u0007\u000f\u0002\u0010\u0007\u0010\u0002\u0011\u0007\u0011"+
		"\u0002\u0012\u0007\u0012\u0002\u0013\u0007\u0013\u0002\u0014\u0007\u0014"+
		"\u0002\u0015\u0007\u0015\u0002\u0016\u0007\u0016\u0002\u0017\u0007\u0017"+
		"\u0002\u0018\u0007\u0018\u0001\u0000\u0001\u0000\u0001\u0001\u0001\u0001"+
		"\u0001\u0002\u0001\u0002\u0001\u0003\u0001\u0003\u0001\u0004\u0004\u0004"+
		"=\b\u0004\u000b\u0004\f\u0004>\u0001\u0005\u0001\u0005\u0001\u0005\u0001"+
		"\u0005\u0001\u0005\u0001\u0005\u0001\u0006\u0001\u0006\u0001\u0006\u0001"+
		"\u0006\u0001\u0006\u0001\u0007\u0001\u0007\u0001\b\u0001\b\u0001\t\u0001"+
		"\t\u0004\tR\b\t\u000b\t\f\tS\u0001\t\u0001\t\u0001\n\u0001\n\u0001\u000b"+
		"\u0001\u000b\u0001\f\u0001\f\u0001\r\u0004\r_\b\r\u000b\r\f\r`\u0001\r"+
		"\u0001\r\u0001\u000e\u0001\u000e\u0001\u000f\u0001\u000f\u0001\u0010\u0001"+
		"\u0010\u0001\u0011\u0001\u0011\u0001\u0012\u0001\u0012\u0001\u0013\u0001"+
		"\u0013\u0001\u0014\u0001\u0014\u0001\u0014\u0001\u0014\u0001\u0014\u0001"+
		"\u0014\u0001\u0015\u0001\u0015\u0001\u0016\u0001\u0016\u0001\u0016\u0001"+
		"\u0016\u0001\u0016\u0001\u0016\u0001\u0016\u0001\u0016\u0001\u0017\u0004"+
		"\u0017\u0082\b\u0017\u000b\u0017\f\u0017\u0083\u0001\u0017\u0001\u0017"+
		"\u0001\u0018\u0001\u0018\u0005\u0018\u008a\b\u0018\n\u0018\f\u0018\u008d"+
		"\t\u0018\u0000\u0000\u0019\u0001\u0001\u0003\u0002\u0005\u0003\u0007\u0004"+
		"\t\u0005\u000b\u0006\r\u0007\u000f\b\u0011\t\u0013\n\u0015\u000b\u0017"+
		"\f\u0019\r\u001b\u000e\u001d\u000f\u001f\u0010!\u0011#\u0012%\u0013\'"+
		"\u0014)\u0015+\u0016-\u0017/\u00181\u0019\u0001\u0000\u0007\u0001\u0000"+
		"09\u0005\u0000\'\'**01AZaz\u0002\u0000>>\u27e9\u27e9\u0002\u0000\n\n\r"+
		"\r\u0002\u0000\t\t  \u0002\u0000AZaz\u0003\u000009AZaz\u0092\u0000\u0001"+
		"\u0001\u0000\u0000\u0000\u0000\u0003\u0001\u0000\u0000\u0000\u0000\u0005"+
		"\u0001\u0000\u0000\u0000\u0000\u0007\u0001\u0000\u0000\u0000\u0000\t\u0001"+
		"\u0000\u0000\u0000\u0000\u000b\u0001\u0000\u0000\u0000\u0000\r\u0001\u0000"+
		"\u0000\u0000\u0000\u000f\u0001\u0000\u0000\u0000\u0000\u0011\u0001\u0000"+
		"\u0000\u0000\u0000\u0013\u0001\u0000\u0000\u0000\u0000\u0015\u0001\u0000"+
		"\u0000\u0000\u0000\u0017\u0001\u0000\u0000\u0000\u0000\u0019\u0001\u0000"+
		"\u0000\u0000\u0000\u001b\u0001\u0000\u0000\u0000\u0000\u001d\u0001\u0000"+
		"\u0000\u0000\u0000\u001f\u0001\u0000\u0000\u0000\u0000!\u0001\u0000\u0000"+
		"\u0000\u0000#\u0001\u0000\u0000\u0000\u0000%\u0001\u0000\u0000\u0000\u0000"+
		"\'\u0001\u0000\u0000\u0000\u0000)\u0001\u0000\u0000\u0000\u0000+\u0001"+
		"\u0000\u0000\u0000\u0000-\u0001\u0000\u0000\u0000\u0000/\u0001\u0000\u0000"+
		"\u0000\u00001\u0001\u0000\u0000\u0000\u00013\u0001\u0000\u0000\u0000\u0003"+
		"5\u0001\u0000\u0000\u0000\u00057\u0001\u0000\u0000\u0000\u00079\u0001"+
		"\u0000\u0000\u0000\t<\u0001\u0000\u0000\u0000\u000b@\u0001\u0000\u0000"+
		"\u0000\rF\u0001\u0000\u0000\u0000\u000fK\u0001\u0000\u0000\u0000\u0011"+
		"M\u0001\u0000\u0000\u0000\u0013O\u0001\u0000\u0000\u0000\u0015W\u0001"+
		"\u0000\u0000\u0000\u0017Y\u0001\u0000\u0000\u0000\u0019[\u0001\u0000\u0000"+
		"\u0000\u001b^\u0001\u0000\u0000\u0000\u001dd\u0001\u0000\u0000\u0000\u001f"+
		"f\u0001\u0000\u0000\u0000!h\u0001\u0000\u0000\u0000#j\u0001\u0000\u0000"+
		"\u0000%l\u0001\u0000\u0000\u0000\'n\u0001\u0000\u0000\u0000)p\u0001\u0000"+
		"\u0000\u0000+v\u0001\u0000\u0000\u0000-x\u0001\u0000\u0000\u0000/\u0081"+
		"\u0001\u0000\u0000\u00001\u0087\u0001\u0000\u0000\u000034\u0005+\u0000"+
		"\u00004\u0002\u0001\u0000\u0000\u000056\u0005|\u0000\u00006\u0004\u0001"+
		"\u0000\u0000\u000078\u0005,\u0000\u00008\u0006\u0001\u0000\u0000\u0000"+
		"9:\u0005/\u0000\u0000:\b\u0001\u0000\u0000\u0000;=\u0007\u0000\u0000\u0000"+
		"<;\u0001\u0000\u0000\u0000=>\u0001\u0000\u0000\u0000><\u0001\u0000\u0000"+
		"\u0000>?\u0001\u0000\u0000\u0000?\n\u0001\u0000\u0000\u0000@A\u0005e\u0000"+
		"\u0000AB\u0005i\u0000\u0000BC\u00052\u0000\u0000CD\u0005p\u0000\u0000"+
		"DE\u0005i\u0000\u0000E\f\u0001\u0000\u0000\u0000FG\u0005e\u0000\u0000"+
		"GH\u0005i\u0000\u0000HI\u0005p\u0000\u0000IJ\u0005i\u0000\u0000J\u000e"+
		"\u0001\u0000\u0000\u0000KL\u0005=\u0000\u0000L\u0010\u0001\u0000\u0000"+
		"\u0000MN\u0005\u2229\u0000\u0000N\u0012\u0001\u0000\u0000\u0000OQ\u0003"+
		"\u0003\u0001\u0000PR\u0007\u0001\u0000\u0000QP\u0001\u0000\u0000\u0000"+
		"RS\u0001\u0000\u0000\u0000SQ\u0001\u0000\u0000\u0000ST\u0001\u0000\u0000"+
		"\u0000TU\u0001\u0000\u0000\u0000UV\u0007\u0002\u0000\u0000V\u0014\u0001"+
		"\u0000\u0000\u0000WX\u0005(\u0000\u0000X\u0016\u0001\u0000\u0000\u0000"+
		"YZ\u0005{\u0000\u0000Z\u0018\u0001\u0000\u0000\u0000[\\\u0005*\u0000\u0000"+
		"\\\u001a\u0001\u0000\u0000\u0000]_\u0007\u0003\u0000\u0000^]\u0001\u0000"+
		"\u0000\u0000_`\u0001\u0000\u0000\u0000`^\u0001\u0000\u0000\u0000`a\u0001"+
		"\u0000\u0000\u0000ab\u0001\u0000\u0000\u0000bc\u0006\r\u0000\u0000c\u001c"+
		"\u0001\u0000\u0000\u0000de\u0005^\u0000\u0000e\u001e\u0001\u0000\u0000"+
		"\u0000fg\u0005\u2297\u0000\u0000g \u0001\u0000\u0000\u0000hi\u0005)\u0000"+
		"\u0000i\"\u0001\u0000\u0000\u0000jk\u0005}\u0000\u0000k$\u0001\u0000\u0000"+
		"\u0000lm\u0005-\u0000\u0000m&\u0001\u0000\u0000\u0000no\u0005\\\u0000"+
		"\u0000o(\u0001\u0000\u0000\u0000pq\u0005s\u0000\u0000qr\u0005q\u0000\u0000"+
		"rs\u0005r\u0000\u0000st\u0005t\u0000\u0000tu\u00052\u0000\u0000u*\u0001"+
		"\u0000\u0000\u0000vw\u0005\u222a\u0000\u0000w,\u0001\u0000\u0000\u0000"+
		"xy\u0005w\u0000\u0000yz\u0005h\u0000\u0000z{\u0005e\u0000\u0000{|\u0005"+
		"r\u0000\u0000|}\u0005e\u0000\u0000}~\u0001\u0000\u0000\u0000~\u007f\u0006"+
		"\u0016\u0001\u0000\u007f.\u0001\u0000\u0000\u0000\u0080\u0082\u0007\u0004"+
		"\u0000\u0000\u0081\u0080\u0001\u0000\u0000\u0000\u0082\u0083\u0001\u0000"+
		"\u0000\u0000\u0083\u0081\u0001\u0000\u0000\u0000\u0083\u0084\u0001\u0000"+
		"\u0000\u0000\u0084\u0085\u0001\u0000\u0000\u0000\u0085\u0086\u0006\u0017"+
		"\u0002\u0000\u00860\u0001\u0000\u0000\u0000\u0087\u008b\u0007\u0005\u0000"+
		"\u0000\u0088\u008a\u0007\u0006\u0000\u0000\u0089\u0088\u0001\u0000\u0000"+
		"\u0000\u008a\u008d\u0001\u0000\u0000\u0000\u008b\u0089\u0001\u0000\u0000"+
		"\u0000\u008b\u008c\u0001\u0000\u0000\u0000\u008c2\u0001\u0000\u0000\u0000"+
		"\u008d\u008b\u0001\u0000\u0000\u0000\u0006\u0000>S`\u0083\u008b\u0003"+
		"\u0001\r\u0000\u0001\u0016\u0001\u0006\u0000\u0000";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}