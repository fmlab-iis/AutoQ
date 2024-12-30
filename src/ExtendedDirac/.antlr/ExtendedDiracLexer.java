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
		KET=10, LEFT_BRACKET=11, LEFT_CURLY_BRACKET=12, MUL=13, POWER=14, PROD=15, 
		RIGHT_BRACKET=16, RIGHT_CURLY_BRACKET=17, SUB=18, SETMINUS=19, SQRT2=20, 
		UNION=21, WS=22, NAME=23;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"ADD", "BAR", "COMMA", "DIV", "DIGITS", "EI2PI", "EIPI", "EQ", "INTERSECTION", 
			"KET", "LEFT_BRACKET", "LEFT_CURLY_BRACKET", "MUL", "POWER", "PROD", 
			"RIGHT_BRACKET", "RIGHT_CURLY_BRACKET", "SUB", "SETMINUS", "SQRT2", "UNION", 
			"WS", "NAME"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'+'", "'|'", "','", "'/'", null, "'ei2pi'", "'eipi'", "'='", "'\\u2229'", 
			null, "'('", "'{'", "'*'", "'^'", "'\\u2297'", "')'", "'}'", "'-'", "'\\'", 
			"'sqrt2'", "'\\u222A'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "ADD", "BAR", "COMMA", "DIV", "DIGITS", "EI2PI", "EIPI", "EQ", 
			"INTERSECTION", "KET", "LEFT_BRACKET", "LEFT_CURLY_BRACKET", "MUL", "POWER", 
			"PROD", "RIGHT_BRACKET", "RIGHT_CURLY_BRACKET", "SUB", "SETMINUS", "SQRT2", 
			"UNION", "WS", "NAME"
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

	public static final String _serializedATN =
		"\u0004\u0000\u0017{\u0006\uffff\uffff\u0002\u0000\u0007\u0000\u0002\u0001"+
		"\u0007\u0001\u0002\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004"+
		"\u0007\u0004\u0002\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007"+
		"\u0007\u0007\u0002\b\u0007\b\u0002\t\u0007\t\u0002\n\u0007\n\u0002\u000b"+
		"\u0007\u000b\u0002\f\u0007\f\u0002\r\u0007\r\u0002\u000e\u0007\u000e\u0002"+
		"\u000f\u0007\u000f\u0002\u0010\u0007\u0010\u0002\u0011\u0007\u0011\u0002"+
		"\u0012\u0007\u0012\u0002\u0013\u0007\u0013\u0002\u0014\u0007\u0014\u0002"+
		"\u0015\u0007\u0015\u0002\u0016\u0007\u0016\u0001\u0000\u0001\u0000\u0001"+
		"\u0001\u0001\u0001\u0001\u0002\u0001\u0002\u0001\u0003\u0001\u0003\u0001"+
		"\u0004\u0004\u00049\b\u0004\u000b\u0004\f\u0004:\u0001\u0005\u0001\u0005"+
		"\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0006\u0001\u0006"+
		"\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0007\u0001\u0007\u0001\b\u0001"+
		"\b\u0001\t\u0001\t\u0004\tN\b\t\u000b\t\f\tO\u0001\t\u0001\t\u0001\n\u0001"+
		"\n\u0001\u000b\u0001\u000b\u0001\f\u0001\f\u0001\r\u0001\r\u0001\u000e"+
		"\u0001\u000e\u0001\u000f\u0001\u000f\u0001\u0010\u0001\u0010\u0001\u0011"+
		"\u0001\u0011\u0001\u0012\u0001\u0012\u0001\u0013\u0001\u0013\u0001\u0013"+
		"\u0001\u0013\u0001\u0013\u0001\u0013\u0001\u0014\u0001\u0014\u0001\u0015"+
		"\u0004\u0015o\b\u0015\u000b\u0015\f\u0015p\u0001\u0015\u0001\u0015\u0001"+
		"\u0016\u0001\u0016\u0005\u0016w\b\u0016\n\u0016\f\u0016z\t\u0016\u0000"+
		"\u0000\u0017\u0001\u0001\u0003\u0002\u0005\u0003\u0007\u0004\t\u0005\u000b"+
		"\u0006\r\u0007\u000f\b\u0011\t\u0013\n\u0015\u000b\u0017\f\u0019\r\u001b"+
		"\u000e\u001d\u000f\u001f\u0010!\u0011#\u0012%\u0013\'\u0014)\u0015+\u0016"+
		"-\u0017\u0001\u0000\u0006\u0001\u000009\u0005\u0000\'\'**01AZaz\u0002"+
		"\u0000>>\u27e9\u27e9\u0003\u0000\t\n\r\r  \u0002\u0000AZaz\u0003\u0000"+
		"09AZaz~\u0000\u0001\u0001\u0000\u0000\u0000\u0000\u0003\u0001\u0000\u0000"+
		"\u0000\u0000\u0005\u0001\u0000\u0000\u0000\u0000\u0007\u0001\u0000\u0000"+
		"\u0000\u0000\t\u0001\u0000\u0000\u0000\u0000\u000b\u0001\u0000\u0000\u0000"+
		"\u0000\r\u0001\u0000\u0000\u0000\u0000\u000f\u0001\u0000\u0000\u0000\u0000"+
		"\u0011\u0001\u0000\u0000\u0000\u0000\u0013\u0001\u0000\u0000\u0000\u0000"+
		"\u0015\u0001\u0000\u0000\u0000\u0000\u0017\u0001\u0000\u0000\u0000\u0000"+
		"\u0019\u0001\u0000\u0000\u0000\u0000\u001b\u0001\u0000\u0000\u0000\u0000"+
		"\u001d\u0001\u0000\u0000\u0000\u0000\u001f\u0001\u0000\u0000\u0000\u0000"+
		"!\u0001\u0000\u0000\u0000\u0000#\u0001\u0000\u0000\u0000\u0000%\u0001"+
		"\u0000\u0000\u0000\u0000\'\u0001\u0000\u0000\u0000\u0000)\u0001\u0000"+
		"\u0000\u0000\u0000+\u0001\u0000\u0000\u0000\u0000-\u0001\u0000\u0000\u0000"+
		"\u0001/\u0001\u0000\u0000\u0000\u00031\u0001\u0000\u0000\u0000\u00053"+
		"\u0001\u0000\u0000\u0000\u00075\u0001\u0000\u0000\u0000\t8\u0001\u0000"+
		"\u0000\u0000\u000b<\u0001\u0000\u0000\u0000\rB\u0001\u0000\u0000\u0000"+
		"\u000fG\u0001\u0000\u0000\u0000\u0011I\u0001\u0000\u0000\u0000\u0013K"+
		"\u0001\u0000\u0000\u0000\u0015S\u0001\u0000\u0000\u0000\u0017U\u0001\u0000"+
		"\u0000\u0000\u0019W\u0001\u0000\u0000\u0000\u001bY\u0001\u0000\u0000\u0000"+
		"\u001d[\u0001\u0000\u0000\u0000\u001f]\u0001\u0000\u0000\u0000!_\u0001"+
		"\u0000\u0000\u0000#a\u0001\u0000\u0000\u0000%c\u0001\u0000\u0000\u0000"+
		"\'e\u0001\u0000\u0000\u0000)k\u0001\u0000\u0000\u0000+n\u0001\u0000\u0000"+
		"\u0000-t\u0001\u0000\u0000\u0000/0\u0005+\u0000\u00000\u0002\u0001\u0000"+
		"\u0000\u000012\u0005|\u0000\u00002\u0004\u0001\u0000\u0000\u000034\u0005"+
		",\u0000\u00004\u0006\u0001\u0000\u0000\u000056\u0005/\u0000\u00006\b\u0001"+
		"\u0000\u0000\u000079\u0007\u0000\u0000\u000087\u0001\u0000\u0000\u0000"+
		"9:\u0001\u0000\u0000\u0000:8\u0001\u0000\u0000\u0000:;\u0001\u0000\u0000"+
		"\u0000;\n\u0001\u0000\u0000\u0000<=\u0005e\u0000\u0000=>\u0005i\u0000"+
		"\u0000>?\u00052\u0000\u0000?@\u0005p\u0000\u0000@A\u0005i\u0000\u0000"+
		"A\f\u0001\u0000\u0000\u0000BC\u0005e\u0000\u0000CD\u0005i\u0000\u0000"+
		"DE\u0005p\u0000\u0000EF\u0005i\u0000\u0000F\u000e\u0001\u0000\u0000\u0000"+
		"GH\u0005=\u0000\u0000H\u0010\u0001\u0000\u0000\u0000IJ\u0005\u2229\u0000"+
		"\u0000J\u0012\u0001\u0000\u0000\u0000KM\u0003\u0003\u0001\u0000LN\u0007"+
		"\u0001\u0000\u0000ML\u0001\u0000\u0000\u0000NO\u0001\u0000\u0000\u0000"+
		"OM\u0001\u0000\u0000\u0000OP\u0001\u0000\u0000\u0000PQ\u0001\u0000\u0000"+
		"\u0000QR\u0007\u0002\u0000\u0000R\u0014\u0001\u0000\u0000\u0000ST\u0005"+
		"(\u0000\u0000T\u0016\u0001\u0000\u0000\u0000UV\u0005{\u0000\u0000V\u0018"+
		"\u0001\u0000\u0000\u0000WX\u0005*\u0000\u0000X\u001a\u0001\u0000\u0000"+
		"\u0000YZ\u0005^\u0000\u0000Z\u001c\u0001\u0000\u0000\u0000[\\\u0005\u2297"+
		"\u0000\u0000\\\u001e\u0001\u0000\u0000\u0000]^\u0005)\u0000\u0000^ \u0001"+
		"\u0000\u0000\u0000_`\u0005}\u0000\u0000`\"\u0001\u0000\u0000\u0000ab\u0005"+
		"-\u0000\u0000b$\u0001\u0000\u0000\u0000cd\u0005\\\u0000\u0000d&\u0001"+
		"\u0000\u0000\u0000ef\u0005s\u0000\u0000fg\u0005q\u0000\u0000gh\u0005r"+
		"\u0000\u0000hi\u0005t\u0000\u0000ij\u00052\u0000\u0000j(\u0001\u0000\u0000"+
		"\u0000kl\u0005\u222a\u0000\u0000l*\u0001\u0000\u0000\u0000mo\u0007\u0003"+
		"\u0000\u0000nm\u0001\u0000\u0000\u0000op\u0001\u0000\u0000\u0000pn\u0001"+
		"\u0000\u0000\u0000pq\u0001\u0000\u0000\u0000qr\u0001\u0000\u0000\u0000"+
		"rs\u0006\u0015\u0000\u0000s,\u0001\u0000\u0000\u0000tx\u0007\u0004\u0000"+
		"\u0000uw\u0007\u0005\u0000\u0000vu\u0001\u0000\u0000\u0000wz\u0001\u0000"+
		"\u0000\u0000xv\u0001\u0000\u0000\u0000xy\u0001\u0000\u0000\u0000y.\u0001"+
		"\u0000\u0000\u0000zx\u0001\u0000\u0000\u0000\u0005\u0000:Opx\u0001\u0006"+
		"\u0000\u0000";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}