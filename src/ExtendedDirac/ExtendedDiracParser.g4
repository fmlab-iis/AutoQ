parser grammar ExtendedDiracParser;

options { tokenVocab=ExtendedDiracLexer; }

@members {
    bool isSymbolicAutomaton = false;
    std::set<std::string> predefinedVars;

    bool isNonZero(const std::string& text) {
        return std::stoi(text) != 0;
    }
    bool isASingleLetter(const std::string& text) {
        return text.length() == 1 && 'a' <= text.at(0) && text.at(0) <= 'z';
    }
}

extendedDirac: accepted (WHERE NEWLINES muloperators)? EOF // EOF is important to ensure that the whole input is parsed.
    ;

muloperators: muloperator+
    ;

muloperator: complex PROD complex '=' complex (NEWLINES|EOF)  // We don't use MUL here because "complex"es may also contain MUL.
    ;

accepted: set
    | set SETMINUS set
    ;

set: set POWER n=DIGITS {isNonZero($n.text)}?
    | LEFT_BRACKET set RIGHT_BRACKET
    | LEFT_CURLY_BRACKET diracs RIGHT_CURLY_BRACKET
    | LEFT_CURLY_BRACKET dirac BAR ijklens RIGHT_CURLY_BRACKET
    | set op=PROD set
    | set op=(UNION|INTERSECTION) set
    ;

diracs: dirac
    | diracs COMMA dirac
    ;

dirac: cket
    | dirac op=(ADD|SUB) cket
    ;

cket: (complex | complex op=MUL | SUB)? KET {
        std::string text = $KET.text;           // Get the full text of the KET token
        std::string state = text.substr(1, text.length() - 2); // Remove the first and last characters
    };

complex: complex POWER n=DIGITS {isNonZero($n.text)}?
    | complex op=(MUL|DIV)? complex
    | complex op=(ADD|SUB) complex
    | LEFT_BRACKET complex RIGHT_BRACKET
    | SUB complex
    | EI2PI LEFT_BRACKET angle RIGHT_BRACKET
    | EIPI LEFT_BRACKET angle RIGHT_BRACKET
    | DIGITS
    | SQRT2
    | var=NAME { if (!predefinedVars.contains($var.text)) isSymbolicAutomaton = true; }
    ;

angle: SUB? x=DIGITS DIV y=DIGITS {isNonZero($y.text)}?
    | SUB? n=DIGITS
    ;

ijklens: ijklen
    | ijklens COMMA ijklen
    ;

ijklen: BAR var=NAME BAR EQ len=DIGITS {isASingleLetter($var.text) && isNonZero($len.text)}?
    ;

// In the project root folder, execute:
// antlr4 -Dlanguage=Cpp -visitor src/ExtendedDirac/ExtendedDiracLexer.g4 && antlr4 -Dlanguage=Cpp -visitor src/ExtendedDirac/ExtendedDiracParser.g4 && mv src/ExtendedDirac/*.h include/autoq/parsing/ExtendedDirac/ && make release