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
		MUL=9, NE=10, NEWLINES=11, OR=12, POWER=13, PRIME=14, PROD=15, RIGHT_ANGLE_BRACKET=16, 
		RIGHT_PARENTHESIS=17, RIGHT_BRACE=18, SEMICOLON=19, SETMINUS=20, STR=21, 
		SUB=22, SUM=23, UNION=24, WS=25;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"ADD", "BAR", "COMMA", "COLON", "DIV", "EQ", "LEFT_PARENTHESIS", "LEFT_BRACE", 
			"MUL", "NE", "NEWLINES", "OR", "POWER", "PRIME", "PROD", "RIGHT_ANGLE_BRACKET", 
			"RIGHT_PARENTHESIS", "RIGHT_BRACE", "SEMICOLON", "SETMINUS", "STR", "SUB", 
			"SUM", "UNION", "WS"
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
		"\u0004\u0000\u0019t\u0006\uffff\uffff\u0002\u0000\u0007\u0000\u0002\u0001"+
		"\u0007\u0001\u0002\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004"+
		"\u0007\u0004\u0002\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007"+
		"\u0007\u0007\u0002\b\u0007\b\u0002\t\u0007\t\u0002\n\u0007\n\u0002\u000b"+
		"\u0007\u000b\u0002\f\u0007\f\u0002\r\u0007\r\u0002\u000e\u0007\u000e\u0002"+
		"\u000f\u0007\u000f\u0002\u0010\u0007\u0010\u0002\u0011\u0007\u0011\u0002"+
		"\u0012\u0007\u0012\u0002\u0013\u0007\u0013\u0002\u0014\u0007\u0014\u0002"+
		"\u0015\u0007\u0015\u0002\u0016\u0007\u0016\u0002\u0017\u0007\u0017\u0002"+
		"\u0018\u0007\u0018\u0001\u0000\u0001\u0000\u0001\u0001\u0001\u0001\u0001"+
		"\u0002\u0001\u0002\u0001\u0003\u0001\u0003\u0001\u0004\u0001\u0004\u0001"+
		"\u0005\u0001\u0005\u0001\u0006\u0001\u0006\u0001\u0007\u0001\u0007\u0001"+
		"\b\u0001\b\u0001\t\u0001\t\u0001\n\u0004\nI\b\n\u000b\n\f\nJ\u0001\n\u0001"+
		"\n\u0001\u000b\u0001\u000b\u0001\f\u0001\f\u0001\r\u0001\r\u0001\u000e"+
		"\u0001\u000e\u0001\u000f\u0001\u000f\u0001\u0010\u0001\u0010\u0001\u0011"+
		"\u0001\u0011\u0001\u0012\u0001\u0012\u0001\u0013\u0001\u0013\u0001\u0014"+
		"\u0001\u0014\u0001\u0014\u0004\u0014d\b\u0014\u000b\u0014\f\u0014e\u0001"+
		"\u0015\u0001\u0015\u0001\u0016\u0001\u0016\u0001\u0017\u0001\u0017\u0001"+
		"\u0018\u0004\u0018o\b\u0018\u000b\u0018\f\u0018p\u0001\u0018\u0001\u0018"+
		"\u0000\u0000\u0019\u0001\u0001\u0003\u0002\u0005\u0003\u0007\u0004\t\u0005"+
		"\u000b\u0006\r\u0007\u000f\b\u0011\t\u0013\n\u0015\u000b\u0017\f\u0019"+
		"\r\u001b\u000e\u001d\u000f\u001f\u0010!\u0011#\u0012%\u0013\'\u0014)\u0015"+
		"+\u0016-\u0017/\u00181\u0019\u0001\u0000\u0006\u0002\u0000\n\n\r\r\u0002"+
		"\u0000>>\u27e9\u27e9\u0003\u000009AZaz\u0001\u0000az\u0002\u0000\u03a3"+
		"\u03a3\u2211\u2211\u0002\u0000\t\t  w\u0000\u0001\u0001\u0000\u0000\u0000"+
		"\u0000\u0003\u0001\u0000\u0000\u0000\u0000\u0005\u0001\u0000\u0000\u0000"+
		"\u0000\u0007\u0001\u0000\u0000\u0000\u0000\t\u0001\u0000\u0000\u0000\u0000"+
		"\u000b\u0001\u0000\u0000\u0000\u0000\r\u0001\u0000\u0000\u0000\u0000\u000f"+
		"\u0001\u0000\u0000\u0000\u0000\u0011\u0001\u0000\u0000\u0000\u0000\u0013"+
		"\u0001\u0000\u0000\u0000\u0000\u0015\u0001\u0000\u0000\u0000\u0000\u0017"+
		"\u0001\u0000\u0000\u0000\u0000\u0019\u0001\u0000\u0000\u0000\u0000\u001b"+
		"\u0001\u0000\u0000\u0000\u0000\u001d\u0001\u0000\u0000\u0000\u0000\u001f"+
		"\u0001\u0000\u0000\u0000\u0000!\u0001\u0000\u0000\u0000\u0000#\u0001\u0000"+
		"\u0000\u0000\u0000%\u0001\u0000\u0000\u0000\u0000\'\u0001\u0000\u0000"+
		"\u0000\u0000)\u0001\u0000\u0000\u0000\u0000+\u0001\u0000\u0000\u0000\u0000"+
		"-\u0001\u0000\u0000\u0000\u0000/\u0001\u0000\u0000\u0000\u00001\u0001"+
		"\u0000\u0000\u0000\u00013\u0001\u0000\u0000\u0000\u00035\u0001\u0000\u0000"+
		"\u0000\u00057\u0001\u0000\u0000\u0000\u00079\u0001\u0000\u0000\u0000\t"+
		";\u0001\u0000\u0000\u0000\u000b=\u0001\u0000\u0000\u0000\r?\u0001\u0000"+
		"\u0000\u0000\u000fA\u0001\u0000\u0000\u0000\u0011C\u0001\u0000\u0000\u0000"+
		"\u0013E\u0001\u0000\u0000\u0000\u0015H\u0001\u0000\u0000\u0000\u0017N"+
		"\u0001\u0000\u0000\u0000\u0019P\u0001\u0000\u0000\u0000\u001bR\u0001\u0000"+
		"\u0000\u0000\u001dT\u0001\u0000\u0000\u0000\u001fV\u0001\u0000\u0000\u0000"+
		"!X\u0001\u0000\u0000\u0000#Z\u0001\u0000\u0000\u0000%\\\u0001\u0000\u0000"+
		"\u0000\'^\u0001\u0000\u0000\u0000)c\u0001\u0000\u0000\u0000+g\u0001\u0000"+
		"\u0000\u0000-i\u0001\u0000\u0000\u0000/k\u0001\u0000\u0000\u00001n\u0001"+
		"\u0000\u0000\u000034\u0005+\u0000\u00004\u0002\u0001\u0000\u0000\u0000"+
		"56\u0005|\u0000\u00006\u0004\u0001\u0000\u0000\u000078\u0005,\u0000\u0000"+
		"8\u0006\u0001\u0000\u0000\u00009:\u0005:\u0000\u0000:\b\u0001\u0000\u0000"+
		"\u0000;<\u0005/\u0000\u0000<\n\u0001\u0000\u0000\u0000=>\u0005=\u0000"+
		"\u0000>\f\u0001\u0000\u0000\u0000?@\u0005(\u0000\u0000@\u000e\u0001\u0000"+
		"\u0000\u0000AB\u0005{\u0000\u0000B\u0010\u0001\u0000\u0000\u0000CD\u0005"+
		"*\u0000\u0000D\u0012\u0001\u0000\u0000\u0000EF\u0005\u2260\u0000\u0000"+
		"F\u0014\u0001\u0000\u0000\u0000GI\u0007\u0000\u0000\u0000HG\u0001\u0000"+
		"\u0000\u0000IJ\u0001\u0000\u0000\u0000JH\u0001\u0000\u0000\u0000JK\u0001"+
		"\u0000\u0000\u0000KL\u0001\u0000\u0000\u0000LM\u0006\n\u0000\u0000M\u0016"+
		"\u0001\u0000\u0000\u0000NO\u0005\u2228\u0000\u0000O\u0018\u0001\u0000"+
		"\u0000\u0000PQ\u0005^\u0000\u0000Q\u001a\u0001\u0000\u0000\u0000RS\u0005"+
		"\'\u0000\u0000S\u001c\u0001\u0000\u0000\u0000TU\u0005\u2297\u0000\u0000"+
		"U\u001e\u0001\u0000\u0000\u0000VW\u0007\u0001\u0000\u0000W \u0001\u0000"+
		"\u0000\u0000XY\u0005)\u0000\u0000Y\"\u0001\u0000\u0000\u0000Z[\u0005}"+
		"\u0000\u0000[$\u0001\u0000\u0000\u0000\\]\u0005;\u0000\u0000]&\u0001\u0000"+
		"\u0000\u0000^_\u0005\\\u0000\u0000_(\u0001\u0000\u0000\u0000`d\u0007\u0002"+
		"\u0000\u0000ab\u0007\u0003\u0000\u0000bd\u0003\u001b\r\u0000c`\u0001\u0000"+
		"\u0000\u0000ca\u0001\u0000\u0000\u0000de\u0001\u0000\u0000\u0000ec\u0001"+
		"\u0000\u0000\u0000ef\u0001\u0000\u0000\u0000f*\u0001\u0000\u0000\u0000"+
		"gh\u0005-\u0000\u0000h,\u0001\u0000\u0000\u0000ij\u0007\u0004\u0000\u0000"+
		"j.\u0001\u0000\u0000\u0000kl\u0005\u222a\u0000\u0000l0\u0001\u0000\u0000"+
		"\u0000mo\u0007\u0005\u0000\u0000nm\u0001\u0000\u0000\u0000op\u0001\u0000"+
		"\u0000\u0000pn\u0001\u0000\u0000\u0000pq\u0001\u0000\u0000\u0000qr\u0001"+
		"\u0000\u0000\u0000rs\u0006\u0018\u0001\u0000s2\u0001\u0000\u0000\u0000"+
		"\u0005\u0000Jcep\u0002\u0001\n\u0000\u0006\u0000\u0000";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}