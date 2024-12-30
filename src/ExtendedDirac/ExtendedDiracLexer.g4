lexer grammar ExtendedDiracLexer;

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
POWER: '^';
PROD: '⊗';
RIGHT_BRACKET: ')';
RIGHT_CURLY_BRACKET: '}';
SUB: '-';
SETMINUS: '\\';
SQRT2: 'sqrt2';
UNION: '∪';
WS: [ \t\r\n]+ -> skip;

NAME: [A-Za-z][A-Za-z0-9]*;