lexer grammar ExtendedDiracLexer;

@members {
    bool skipNewline = true;
}

ADD: '+';
BAR: '|';
COMMA: ',';
COLON: ':';
// DIV: '/';
// DIGITS: [0-9]+;
// EI2PI: 'ei2pi';
// EIPI: 'eipi';
EQ: '=';
// INTERSECTION: '∩';
// KET: BAR  RIGHT_ANGLE_BRACKET;
// LEFT_PARENTHESIS: '(';
LEFT_BRACE: '{';
// MUL: '*';
NE: '≠';
NEWLINES: [\r\n]+ { if (skipNewline) skip(); };
OR: '∨';
POWER: '^';
PRIME: '\'';
PROD: '⊗';
RIGHT_ANGLE_BRACKET: '⟩' | '>';
// RIGHT_PARENTHESIS: ')';
RIGHT_BRACE: '}';
SEMICOLON: ';';
SETMINUS: '\\';
STR: ([0-9a-zA-Z]|[a-z]PRIME)+; // *
// SUB: '-';
SUM: '∑' | 'Σ';
// SQRT2: 'sqrt2';
UNION: '∪'; // | 'U'; // Notice that U may be confused with the bit-complemented variable's name.
// WHERE: 'where' { skipNewline = false; };
WS: [ \t]+ -> skip;

// NAME: [A-Za-z][A-Za-z0-9]*; // the most general rule must be put at the end