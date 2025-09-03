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
		ADD=1, BAR=2, COMMA=3, COLON=4, DIV=5, EQ=6, LEFT_PARENTHESIS=7, LEFT_BRACE=8, 
		MUL=9, NE=10, NEWLINES=11, POWER=12, PRIME=13, PROD=14, RIGHT_ANGLE_BRACKET=15, 
		RIGHT_PARENTHESIS=16, RIGHT_BRACE=17, SEMICOLON=18, SETMINUS=19, STR=20, 
		SUB=21, SUM=22, UNION=23, WS=24, LOGICAL_AND=25, LOGICAL_OR=26, LOGICAL_NOT=27, 
		LESS_THAN=28, LESS_EQUAL=29, GREATER_EQUAL=30;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"ADD", "BAR", "COMMA", "COLON", "DIV", "EQ", "LEFT_PARENTHESIS", "LEFT_BRACE", 
			"MUL", "NE", "NEWLINES", "POWER", "PRIME", "PROD", "RIGHT_ANGLE_BRACKET", 
			"RIGHT_PARENTHESIS", "RIGHT_BRACE", "SEMICOLON", "SETMINUS", "STR", "SUB", 
			"SUM", "UNION", "WS", "LOGICAL_AND", "LOGICAL_OR", "LOGICAL_NOT", "LESS_THAN", 
			"LESS_EQUAL", "GREATER_EQUAL"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'+'", "'|'", "','", "':'", "'/'", "'='", "'('", "'{'", "'*'", 
			null, null, "'^'", "'''", "'\\u2297'", null, "')'", "'}'", "';'", "'\\'", 
			null, "'-'", null, "'\\u222A'", null, null, null, null, "'<'"
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
		case 10:
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
		"\u0004\u0000\u001e\u0097\u0006\uffff\uffff\u0002\u0000\u0007\u0000\u0002"+
		"\u0001\u0007\u0001\u0002\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002"+
		"\u0004\u0007\u0004\u0002\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002"+
		"\u0007\u0007\u0007\u0002\b\u0007\b\u0002\t\u0007\t\u0002\n\u0007\n\u0002"+
		"\u000b\u0007\u000b\u0002\f\u0007\f\u0002\r\u0007\r\u0002\u000e\u0007\u000e"+
		"\u0002\u000f\u0007\u000f\u0002\u0010\u0007\u0010\u0002\u0011\u0007\u0011"+
		"\u0002\u0012\u0007\u0012\u0002\u0013\u0007\u0013\u0002\u0014\u0007\u0014"+
		"\u0002\u0015\u0007\u0015\u0002\u0016\u0007\u0016\u0002\u0017\u0007\u0017"+
		"\u0002\u0018\u0007\u0018\u0002\u0019\u0007\u0019\u0002\u001a\u0007\u001a"+
		"\u0002\u001b\u0007\u001b\u0002\u001c\u0007\u001c\u0002\u001d\u0007\u001d"+
		"\u0001\u0000\u0001\u0000\u0001\u0001\u0001\u0001\u0001\u0002\u0001\u0002"+
		"\u0001\u0003\u0001\u0003\u0001\u0004\u0001\u0004\u0001\u0005\u0001\u0005"+
		"\u0001\u0006\u0001\u0006\u0001\u0007\u0001\u0007\u0001\b\u0001\b\u0001"+
		"\t\u0001\t\u0001\t\u0003\tS\b\t\u0001\n\u0004\nV\b\n\u000b\n\f\nW\u0001"+
		"\n\u0001\n\u0001\u000b\u0001\u000b\u0001\f\u0001\f\u0001\r\u0001\r\u0001"+
		"\u000e\u0001\u000e\u0001\u000f\u0001\u000f\u0001\u0010\u0001\u0010\u0001"+
		"\u0011\u0001\u0011\u0001\u0012\u0001\u0012\u0001\u0013\u0001\u0013\u0001"+
		"\u0013\u0004\u0013o\b\u0013\u000b\u0013\f\u0013p\u0001\u0014\u0001\u0014"+
		"\u0001\u0015\u0001\u0015\u0001\u0016\u0001\u0016\u0001\u0017\u0004\u0017"+
		"z\b\u0017\u000b\u0017\f\u0017{\u0001\u0017\u0001\u0017\u0001\u0018\u0001"+
		"\u0018\u0001\u0018\u0003\u0018\u0083\b\u0018\u0001\u0019\u0001\u0019\u0001"+
		"\u0019\u0003\u0019\u0088\b\u0019\u0001\u001a\u0001\u001a\u0001\u001b\u0001"+
		"\u001b\u0001\u001c\u0001\u001c\u0001\u001c\u0003\u001c\u0091\b\u001c\u0001"+
		"\u001d\u0001\u001d\u0001\u001d\u0003\u001d\u0096\b\u001d\u0000\u0000\u001e"+
		"\u0001\u0001\u0003\u0002\u0005\u0003\u0007\u0004\t\u0005\u000b\u0006\r"+
		"\u0007\u000f\b\u0011\t\u0013\n\u0015\u000b\u0017\f\u0019\r\u001b\u000e"+
		"\u001d\u000f\u001f\u0010!\u0011#\u0012%\u0013\'\u0014)\u0015+\u0016-\u0017"+
		"/\u00181\u00193\u001a5\u001b7\u001c9\u001d;\u001e\u0001\u0000\t\u0002"+
		"\u0000\n\n\r\r\u0002\u0000>>\u27e9\u27e9\u0003\u000009AZaz\u0001\u0000"+
		"az\u0002\u0000\u03a3\u03a3\u2211\u2211\u0002\u0000\t\t  \u0002\u0000!"+
		"!\u00ac\u00ac\u0002\u0000\u2264\u2264\u2266\u2266\u0002\u0000\u2265\u2265"+
		"\u2267\u2267\u009f\u0000\u0001\u0001\u0000\u0000\u0000\u0000\u0003\u0001"+
		"\u0000\u0000\u0000\u0000\u0005\u0001\u0000\u0000\u0000\u0000\u0007\u0001"+
		"\u0000\u0000\u0000\u0000\t\u0001\u0000\u0000\u0000\u0000\u000b\u0001\u0000"+
		"\u0000\u0000\u0000\r\u0001\u0000\u0000\u0000\u0000\u000f\u0001\u0000\u0000"+
		"\u0000\u0000\u0011\u0001\u0000\u0000\u0000\u0000\u0013\u0001\u0000\u0000"+
		"\u0000\u0000\u0015\u0001\u0000\u0000\u0000\u0000\u0017\u0001\u0000\u0000"+
		"\u0000\u0000\u0019\u0001\u0000\u0000\u0000\u0000\u001b\u0001\u0000\u0000"+
		"\u0000\u0000\u001d\u0001\u0000\u0000\u0000\u0000\u001f\u0001\u0000\u0000"+
		"\u0000\u0000!\u0001\u0000\u0000\u0000\u0000#\u0001\u0000\u0000\u0000\u0000"+
		"%\u0001\u0000\u0000\u0000\u0000\'\u0001\u0000\u0000\u0000\u0000)\u0001"+
		"\u0000\u0000\u0000\u0000+\u0001\u0000\u0000\u0000\u0000-\u0001\u0000\u0000"+
		"\u0000\u0000/\u0001\u0000\u0000\u0000\u00001\u0001\u0000\u0000\u0000\u0000"+
		"3\u0001\u0000\u0000\u0000\u00005\u0001\u0000\u0000\u0000\u00007\u0001"+
		"\u0000\u0000\u0000\u00009\u0001\u0000\u0000\u0000\u0000;\u0001\u0000\u0000"+
		"\u0000\u0001=\u0001\u0000\u0000\u0000\u0003?\u0001\u0000\u0000\u0000\u0005"+
		"A\u0001\u0000\u0000\u0000\u0007C\u0001\u0000\u0000\u0000\tE\u0001\u0000"+
		"\u0000\u0000\u000bG\u0001\u0000\u0000\u0000\rI\u0001\u0000\u0000\u0000"+
		"\u000fK\u0001\u0000\u0000\u0000\u0011M\u0001\u0000\u0000\u0000\u0013R"+
		"\u0001\u0000\u0000\u0000\u0015U\u0001\u0000\u0000\u0000\u0017[\u0001\u0000"+
		"\u0000\u0000\u0019]\u0001\u0000\u0000\u0000\u001b_\u0001\u0000\u0000\u0000"+
		"\u001da\u0001\u0000\u0000\u0000\u001fc\u0001\u0000\u0000\u0000!e\u0001"+
		"\u0000\u0000\u0000#g\u0001\u0000\u0000\u0000%i\u0001\u0000\u0000\u0000"+
		"\'n\u0001\u0000\u0000\u0000)r\u0001\u0000\u0000\u0000+t\u0001\u0000\u0000"+
		"\u0000-v\u0001\u0000\u0000\u0000/y\u0001\u0000\u0000\u00001\u0082\u0001"+
		"\u0000\u0000\u00003\u0087\u0001\u0000\u0000\u00005\u0089\u0001\u0000\u0000"+
		"\u00007\u008b\u0001\u0000\u0000\u00009\u0090\u0001\u0000\u0000\u0000;"+
		"\u0095\u0001\u0000\u0000\u0000=>\u0005+\u0000\u0000>\u0002\u0001\u0000"+
		"\u0000\u0000?@\u0005|\u0000\u0000@\u0004\u0001\u0000\u0000\u0000AB\u0005"+
		",\u0000\u0000B\u0006\u0001\u0000\u0000\u0000CD\u0005:\u0000\u0000D\b\u0001"+
		"\u0000\u0000\u0000EF\u0005/\u0000\u0000F\n\u0001\u0000\u0000\u0000GH\u0005"+
		"=\u0000\u0000H\f\u0001\u0000\u0000\u0000IJ\u0005(\u0000\u0000J\u000e\u0001"+
		"\u0000\u0000\u0000KL\u0005{\u0000\u0000L\u0010\u0001\u0000\u0000\u0000"+
		"MN\u0005*\u0000\u0000N\u0012\u0001\u0000\u0000\u0000OS\u0005\u2260\u0000"+
		"\u0000PQ\u0005!\u0000\u0000QS\u0005=\u0000\u0000RO\u0001\u0000\u0000\u0000"+
		"RP\u0001\u0000\u0000\u0000S\u0014\u0001\u0000\u0000\u0000TV\u0007\u0000"+
		"\u0000\u0000UT\u0001\u0000\u0000\u0000VW\u0001\u0000\u0000\u0000WU\u0001"+
		"\u0000\u0000\u0000WX\u0001\u0000\u0000\u0000XY\u0001\u0000\u0000\u0000"+
		"YZ\u0006\n\u0000\u0000Z\u0016\u0001\u0000\u0000\u0000[\\\u0005^\u0000"+
		"\u0000\\\u0018\u0001\u0000\u0000\u0000]^\u0005\'\u0000\u0000^\u001a\u0001"+
		"\u0000\u0000\u0000_`\u0005\u2297\u0000\u0000`\u001c\u0001\u0000\u0000"+
		"\u0000ab\u0007\u0001\u0000\u0000b\u001e\u0001\u0000\u0000\u0000cd\u0005"+
		")\u0000\u0000d \u0001\u0000\u0000\u0000ef\u0005}\u0000\u0000f\"\u0001"+
		"\u0000\u0000\u0000gh\u0005;\u0000\u0000h$\u0001\u0000\u0000\u0000ij\u0005"+
		"\\\u0000\u0000j&\u0001\u0000\u0000\u0000ko\u0007\u0002\u0000\u0000lm\u0007"+
		"\u0003\u0000\u0000mo\u0003\u0019\f\u0000nk\u0001\u0000\u0000\u0000nl\u0001"+
		"\u0000\u0000\u0000op\u0001\u0000\u0000\u0000pn\u0001\u0000\u0000\u0000"+
		"pq\u0001\u0000\u0000\u0000q(\u0001\u0000\u0000\u0000rs\u0005-\u0000\u0000"+
		"s*\u0001\u0000\u0000\u0000tu\u0007\u0004\u0000\u0000u,\u0001\u0000\u0000"+
		"\u0000vw\u0005\u222a\u0000\u0000w.\u0001\u0000\u0000\u0000xz\u0007\u0005"+
		"\u0000\u0000yx\u0001\u0000\u0000\u0000z{\u0001\u0000\u0000\u0000{y\u0001"+
		"\u0000\u0000\u0000{|\u0001\u0000\u0000\u0000|}\u0001\u0000\u0000\u0000"+
		"}~\u0006\u0017\u0001\u0000~0\u0001\u0000\u0000\u0000\u007f\u0080\u0005"+
		"&\u0000\u0000\u0080\u0083\u0005&\u0000\u0000\u0081\u0083\u0005\u2227\u0000"+
		"\u0000\u0082\u007f\u0001\u0000\u0000\u0000\u0082\u0081\u0001\u0000\u0000"+
		"\u0000\u00832\u0001\u0000\u0000\u0000\u0084\u0085\u0005|\u0000\u0000\u0085"+
		"\u0088\u0005|\u0000\u0000\u0086\u0088\u0005\u2228\u0000\u0000\u0087\u0084"+
		"\u0001\u0000\u0000\u0000\u0087\u0086\u0001\u0000\u0000\u0000\u00884\u0001"+
		"\u0000\u0000\u0000\u0089\u008a\u0007\u0006\u0000\u0000\u008a6\u0001\u0000"+
		"\u0000\u0000\u008b\u008c\u0005<\u0000\u0000\u008c8\u0001\u0000\u0000\u0000"+
		"\u008d\u008e\u0005<\u0000\u0000\u008e\u0091\u0005=\u0000\u0000\u008f\u0091"+
		"\u0007\u0007\u0000\u0000\u0090\u008d\u0001\u0000\u0000\u0000\u0090\u008f"+
		"\u0001\u0000\u0000\u0000\u0091:\u0001\u0000\u0000\u0000\u0092\u0093\u0005"+
		">\u0000\u0000\u0093\u0096\u0005=\u0000\u0000\u0094\u0096\u0007\b\u0000"+
		"\u0000\u0095\u0092\u0001\u0000\u0000\u0000\u0095\u0094\u0001\u0000\u0000"+
		"\u0000\u0096<\u0001\u0000\u0000\u0000\n\u0000RWnp{\u0082\u0087\u0090\u0095"+
		"\u0002\u0001\n\u0000\u0006\u0000\u0000";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}