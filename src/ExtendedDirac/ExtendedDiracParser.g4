parser grammar ExtendedDiracParser;

options { tokenVocab=ExtendedDiracLexer; }

@members {
    bool isSymbolicAutomaton = false;
    std::set<std::string> predefinedVars;

    bool isNonZero(const std::string& text) {
        return std::stoi(text) != 0;
    }
    bool isALowercaseLetter(const std::string& text) {
        return text.length() == 1 && 'a' <= text.at(0) && text.at(0) <= 'z';
    }
    bool isAConstantBinaryString(const std::string& text) {
        return std::all_of(text.begin(), text.end(), [](char c) { return c == '0' || c == '1'; });
    }
}

// extendedDirac: accepted (WHERE NEWLINES muloperators)? EOF // EOF is important to ensure that the whole input is parsed.
//     ;

// muloperators: muloperator+
//     ;

// muloperator: complex PROD complex '=' complex (NEWLINES|EOF)  // We don't use MUL here because "complex"es may also contain MUL.
//     ;

// accepted: set
//     | set SETMINUS set
//     ;

expr: tset
    | tset op=SETMINUS tset;

tset: scset
    | set op=POWER N=STR {isNonZero($N.text)}?
    | tset op=PROD tset
    // | set op=SEMICOLON set // used for connecting different *.hsl to compute the unit decomposition together
    // | set op=SEMICOLON set SEMICOLON set // used for connecting different *.hsl to compute the unit decomposition together
    // | set op=SEMICOLON set SEMICOLON set SEMICOLON set // used for connecting different *.hsl to compute the unit decomposition together
    ;

scset: scset op=SEMICOLON set
    | set
    ;

set: set op=UNION set
    | LEFT_BRACE diracs RIGHT_BRACE
    | LEFT_BRACE diracs COLON varcons RIGHT_BRACE
    ;

diracs: dirac
    | diracs COMMA dirac
    ;

dirac: term
    | dirac op=ADD term
    ;

term: C=STR BAR VStr=STR RIGHT_ANGLE_BRACKET
    | C=STR SUM varcons BAR VStr=STR RIGHT_ANGLE_BRACKET
    ;
// (complex | complex op=MUL | SUB)? KET {
//         std::string text = $KET.text;           // Get the full text of the KET token
//         std::string state = text.substr(1, text.length() - 2); // Remove the first and last characters
//     };

// complex: complex POWER n=DIGITS {isNonZero($n.text)}?
//     | complex op=(MUL|DIV)? complex
//     | complex op=(ADD|SUB) complex
//     | LEFT_BRACKET complex RIGHT_BRACKET
//     | SUB complex
//     | EI2PI LEFT_BRACKET angle RIGHT_BRACKET
//     | EIPI LEFT_BRACKET angle RIGHT_BRACKET
//     | DIGITS
//     | SQRT2
//     | var=NAME { if (!predefinedVars.contains($var.text)) isSymbolicAutomaton = true; }
//     ;

// angle: SUB? x=DIGITS DIV y=DIGITS {isNonZero($y.text)}?
//     | SUB? n=DIGITS
//     ;

varcons: varcon
    | varcons COMMA varcon
    ;

varcon: BAR V=STR BAR EQ N=STR {isALowercaseLetter($V.text) && isNonZero($N.text)}? // can check if V is a single letter here
    | V=STR EQ CStr=STR {isALowercaseLetter($V.text) && isAConstantBinaryString($CStr.text)}? // can check if V is a single letter here
    | ineq
    ;

// ineqs: ineq
//     | ineqs OR ineq
//     ;

ineq: L=STR NE R=STR {isALowercaseLetter($L.text) && (isALowercaseLetter($R.text) || isAConstantBinaryString($R.text))}? // R can be a variable or a constant
    ;

// ijklens: ijklen
//     | ijklens COMMA ijklen
//     ;

// ijklen: BAR var=NAME BAR EQ len=DIGITS {isALowercaseLetter($var.text) && isNonZero($len.text)}?
//     ;

// In the project root folder, execute:
// antlr4 -Dlanguage=Cpp -visitor src/ExtendedDirac/ExtendedDiracLexer.g4 && antlr4 -Dlanguage=Cpp -visitor src/ExtendedDirac/ExtendedDiracParser.g4 && mv src/ExtendedDirac/*.h include/autoq/parsing/ExtendedDirac/ && make debug
// antlr4 -Dlanguage=Cpp -visitor src/ExtendedDirac/ExtendedDiracLexer.g4 && antlr4 -Dlanguage=Cpp -visitor src/ExtendedDirac/ExtendedDiracParser.g4 && mv src/ExtendedDirac/*.h include/autoq/parsing/ExtendedDirac/ && make release