lexer grammar ExtendedDiracLexer;

@members {
    bool skipNewline = true;
}

ADD: '+';
BAR: '|';
COMMA: ',';
DIV: '/';
DIGITS: [0-9]+;
EI2PI: 'ei2pi';
EIPI: 'eipi';
EQ: '=';
INTERSECTION: '∩';
KET: BAR [01A-Za-z*']+ ('⟩'|'>');
LEFT_BRACKET: '(';
LEFT_CURLY_BRACKET: '{';
MUL: '*';
NEWLINES: [\r\n]+ { if (skipNewline) skip(); };
POWER: '^';
PROD: '⊗';
RIGHT_BRACKET: ')';
RIGHT_CURLY_BRACKET: '}';
SUB: '-';
SETMINUS: '\\';
SQRT2: 'sqrt2';
UNION: '∪';
WHERE: 'where' { skipNewline = false; };
WS: [ \t]+ -> skip;

NAME: [A-Za-z][A-Za-z0-9]*; // the most general rule must be put at the end