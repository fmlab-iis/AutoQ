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
		ADD=1, BAR=2, COMMA=3, COLON=4, EQ=5, LEFT_BRACE=6, NE=7, NEWLINES=8, 
		OR=9, POWER=10, PRIME=11, PROD=12, RIGHT_ANGLE_BRACKET=13, RIGHT_BRACE=14, 
		SEMICOLON=15, STR=16, SUM=17, UNION=18, WS=19;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"ADD", "BAR", "COMMA", "COLON", "EQ", "LEFT_BRACE", "NE", "NEWLINES", 
			"OR", "POWER", "PRIME", "PROD", "RIGHT_ANGLE_BRACKET", "RIGHT_BRACE", 
			"SEMICOLON", "STR", "SUM", "UNION", "WS"
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
		case 7:
			NEWLINES_action((RuleContext)_localctx, actionIndex);
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

	public static final String _serializedATN =
		"\u0004\u0000\u0013\\\u0006\uffff\uffff\u0002\u0000\u0007\u0000\u0002\u0001"+
		"\u0007\u0001\u0002\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004"+
		"\u0007\u0004\u0002\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007"+
		"\u0007\u0007\u0002\b\u0007\b\u0002\t\u0007\t\u0002\n\u0007\n\u0002\u000b"+
		"\u0007\u000b\u0002\f\u0007\f\u0002\r\u0007\r\u0002\u000e\u0007\u000e\u0002"+
		"\u000f\u0007\u000f\u0002\u0010\u0007\u0010\u0002\u0011\u0007\u0011\u0002"+
		"\u0012\u0007\u0012\u0001\u0000\u0001\u0000\u0001\u0001\u0001\u0001\u0001"+
		"\u0002\u0001\u0002\u0001\u0003\u0001\u0003\u0001\u0004\u0001\u0004\u0001"+
		"\u0005\u0001\u0005\u0001\u0006\u0001\u0006\u0001\u0007\u0004\u00077\b"+
		"\u0007\u000b\u0007\f\u00078\u0001\u0007\u0001\u0007\u0001\b\u0001\b\u0001"+
		"\t\u0001\t\u0001\n\u0001\n\u0001\u000b\u0001\u000b\u0001\f\u0001\f\u0001"+
		"\r\u0001\r\u0001\u000e\u0001\u000e\u0001\u000f\u0001\u000f\u0001\u000f"+
		"\u0004\u000fN\b\u000f\u000b\u000f\f\u000fO\u0001\u0010\u0001\u0010\u0001"+
		"\u0011\u0001\u0011\u0001\u0012\u0004\u0012W\b\u0012\u000b\u0012\f\u0012"+
		"X\u0001\u0012\u0001\u0012\u0000\u0000\u0013\u0001\u0001\u0003\u0002\u0005"+
		"\u0003\u0007\u0004\t\u0005\u000b\u0006\r\u0007\u000f\b\u0011\t\u0013\n"+
		"\u0015\u000b\u0017\f\u0019\r\u001b\u000e\u001d\u000f\u001f\u0010!\u0011"+
		"#\u0012%\u0013\u0001\u0000\u0006\u0002\u0000\n\n\r\r\u0002\u0000>>\u27e9"+
		"\u27e9\u0003\u000009AZaz\u0001\u0000az\u0002\u0000\u03a3\u03a3\u2211\u2211"+
		"\u0002\u0000\t\t  _\u0000\u0001\u0001\u0000\u0000\u0000\u0000\u0003\u0001"+
		"\u0000\u0000\u0000\u0000\u0005\u0001\u0000\u0000\u0000\u0000\u0007\u0001"+
		"\u0000\u0000\u0000\u0000\t\u0001\u0000\u0000\u0000\u0000\u000b\u0001\u0000"+
		"\u0000\u0000\u0000\r\u0001\u0000\u0000\u0000\u0000\u000f\u0001\u0000\u0000"+
		"\u0000\u0000\u0011\u0001\u0000\u0000\u0000\u0000\u0013\u0001\u0000\u0000"+
		"\u0000\u0000\u0015\u0001\u0000\u0000\u0000\u0000\u0017\u0001\u0000\u0000"+
		"\u0000\u0000\u0019\u0001\u0000\u0000\u0000\u0000\u001b\u0001\u0000\u0000"+
		"\u0000\u0000\u001d\u0001\u0000\u0000\u0000\u0000\u001f\u0001\u0000\u0000"+
		"\u0000\u0000!\u0001\u0000\u0000\u0000\u0000#\u0001\u0000\u0000\u0000\u0000"+
		"%\u0001\u0000\u0000\u0000\u0001\'\u0001\u0000\u0000\u0000\u0003)\u0001"+
		"\u0000\u0000\u0000\u0005+\u0001\u0000\u0000\u0000\u0007-\u0001\u0000\u0000"+
		"\u0000\t/\u0001\u0000\u0000\u0000\u000b1\u0001\u0000\u0000\u0000\r3\u0001"+
		"\u0000\u0000\u0000\u000f6\u0001\u0000\u0000\u0000\u0011<\u0001\u0000\u0000"+
		"\u0000\u0013>\u0001\u0000\u0000\u0000\u0015@\u0001\u0000\u0000\u0000\u0017"+
		"B\u0001\u0000\u0000\u0000\u0019D\u0001\u0000\u0000\u0000\u001bF\u0001"+
		"\u0000\u0000\u0000\u001dH\u0001\u0000\u0000\u0000\u001fM\u0001\u0000\u0000"+
		"\u0000!Q\u0001\u0000\u0000\u0000#S\u0001\u0000\u0000\u0000%V\u0001\u0000"+
		"\u0000\u0000\'(\u0005+\u0000\u0000(\u0002\u0001\u0000\u0000\u0000)*\u0005"+
		"|\u0000\u0000*\u0004\u0001\u0000\u0000\u0000+,\u0005,\u0000\u0000,\u0006"+
		"\u0001\u0000\u0000\u0000-.\u0005:\u0000\u0000.\b\u0001\u0000\u0000\u0000"+
		"/0\u0005=\u0000\u00000\n\u0001\u0000\u0000\u000012\u0005{\u0000\u0000"+
		"2\f\u0001\u0000\u0000\u000034\u0005\u2260\u0000\u00004\u000e\u0001\u0000"+
		"\u0000\u000057\u0007\u0000\u0000\u000065\u0001\u0000\u0000\u000078\u0001"+
		"\u0000\u0000\u000086\u0001\u0000\u0000\u000089\u0001\u0000\u0000\u0000"+
		"9:\u0001\u0000\u0000\u0000:;\u0006\u0007\u0000\u0000;\u0010\u0001\u0000"+
		"\u0000\u0000<=\u0005\u2228\u0000\u0000=\u0012\u0001\u0000\u0000\u0000"+
		">?\u0005^\u0000\u0000?\u0014\u0001\u0000\u0000\u0000@A\u0005\'\u0000\u0000"+
		"A\u0016\u0001\u0000\u0000\u0000BC\u0005\u2297\u0000\u0000C\u0018\u0001"+
		"\u0000\u0000\u0000DE\u0007\u0001\u0000\u0000E\u001a\u0001\u0000\u0000"+
		"\u0000FG\u0005}\u0000\u0000G\u001c\u0001\u0000\u0000\u0000HI\u0005;\u0000"+
		"\u0000I\u001e\u0001\u0000\u0000\u0000JN\u0007\u0002\u0000\u0000KL\u0007"+
		"\u0003\u0000\u0000LN\u0003\u0015\n\u0000MJ\u0001\u0000\u0000\u0000MK\u0001"+
		"\u0000\u0000\u0000NO\u0001\u0000\u0000\u0000OM\u0001\u0000\u0000\u0000"+
		"OP\u0001\u0000\u0000\u0000P \u0001\u0000\u0000\u0000QR\u0007\u0004\u0000"+
		"\u0000R\"\u0001\u0000\u0000\u0000ST\u0005\u222a\u0000\u0000T$\u0001\u0000"+
		"\u0000\u0000UW\u0007\u0005\u0000\u0000VU\u0001\u0000\u0000\u0000WX\u0001"+
		"\u0000\u0000\u0000XV\u0001\u0000\u0000\u0000XY\u0001\u0000\u0000\u0000"+
		"YZ\u0001\u0000\u0000\u0000Z[\u0006\u0012\u0001\u0000[&\u0001\u0000\u0000"+
		"\u0000\u0005\u00008MOX\u0002\u0001\u0007\u0000\u0006\u0000\u0000";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}