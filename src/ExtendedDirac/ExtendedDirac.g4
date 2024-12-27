grammar ExtendedDirac;

@parser::members {
    bool isSymbolicAutomaton = false;
    std::set<std::string> predefinedVars;

    bool isNonZero(const std::string& text) {
        return std::stoi(text) != 0;
    }
    bool isASingleLetter(const std::string& text) {
        return text.length() == 1 && 'a' <= text.at(0) && text.at(0) <= 'z';
    }
}

/*******************************************************************
 * TOKENS
 *******************************************************************/
ADD: '+';
DIV: '/';
DIGITS: [0-9]+;
INTERSECTION: '∩';
KET: '|' [01A-Za-z*']+ ('⟩'|'>');
MUL: '*';
NAME: [A-Za-z][A-Za-z0-9]*;
PROD: '⊗';
SUB: '-';
UNION: '∪';

/*******************************************************************
 * GRAMMAR
 *******************************************************************/
extendedDirac: set
    | set '\\' set
    ;

set: set '^' n=DIGITS {isNonZero($n.text)}?
    | '(' set ')'
    | '{' diracs '}'
    | '{' dirac '|' ijklens '}'
    | set op=PROD set
    | set op=(UNION|INTERSECTION) set
    ;

diracs: dirac
    | diracs ',' dirac
    ;

dirac: cket
    | dirac op=(ADD|SUB) cket
    ;

cket: (complex | complex op='*' | '-')? KET {
        std::string text = $KET.text;           // Get the full text of the KET token
        std::string state = text.substr(1, text.length() - 2); // Remove the first and last characters
    };

complex: complex '^' n=DIGITS {isNonZero($n.text)}?
    | complex op=(MUL|DIV)? complex
    | complex op=(ADD|SUB) complex
    | '(' complex ')'
    | '-' complex
    | 'ei2pi(' angle ')'
    | 'eipi(' angle ')'
    | DIGITS
    | 'sqrt2'
    | var=NAME { if (!predefinedVars.contains($var.text)) isSymbolicAutomaton = true; }
    ;

angle: '-'? x=DIGITS '/' y=DIGITS {isNonZero($y.text)}?
    | '-'? n=DIGITS
    ;

ijklens: ijklen
    | ijklens ',' ijklen
    ;

ijklen: '|' var=NAME '|=' len=DIGITS {isASingleLetter($var.text) && isNonZero($len.text)}?
    ;

/*******************************************************************
* THE END
*******************************************************************/

WS: [ \t\r\n]+ -> skip;

// In the project root folder, execute:
// antlr4 -Dlanguage=Cpp -visitor src/ExtendedDirac/ExtendedDirac.g4 && mv src/ExtendedDirac/ExtendedDirac*.h include/autoq/parsing/ExtendedDirac/ && make release