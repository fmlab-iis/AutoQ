#ifndef _AUTOQ_EXTENDED_DIRAC_PARSING_COMMON_HH_
#define _AUTOQ_EXTENDED_DIRAC_PARSING_COMMON_HH_

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wnon-virtual-dtor"
#pragma GCC diagnostic ignored "-Woverloaded-virtual"
#pragma GCC diagnostic ignored "-Weffc++"
#include "ExtendedDiracLexer.h"
#include "ExtendedDiracParserBaseVisitor.h"
#include "ExtendedDiracParser.h"
#pragma GCC diagnostic pop

#include "autoq/error.hh"
#include "autoq/complex/complex.hh"

class CustomErrorListener : public antlr4::BaseErrorListener {
public:
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wunused-parameter"
    void syntaxError(antlr4::Recognizer *recognizer,
                     antlr4::Token *offendingSymbol,
                     size_t line, size_t charPositionInLine,
                     const std::string &msg,
                     std::exception_ptr e) override {
        THROW_AUTOQ_ERROR("Parsing Error: Line " + std::to_string(line) + ":" + std::to_string(charPositionInLine)
              + " in ExtendedDirac.g4 - " + msg);
    }
    #pragma GCC diagnostic pop
};

namespace {
inline const std::map<std::string, AUTOQ::Complex::Complex>& get_empty_const_map() {
    static const std::map<std::string, AUTOQ::Complex::Complex> m{};
    return m;
}

template<typename GetTree>
inline std::any parse_extended_dirac_and_visit(const std::string& input, GetTree get_tree, ExtendedDiracParserBaseVisitor* visitor) {
    antlr4::ANTLRInputStream inputStream(input);
    CustomErrorListener errorListener;
    ExtendedDiracLexer lexer(&inputStream);
    // Unknown characters are lexer errors. Without this listener ANTLR drops
    // the character and keeps parsing (#25), so 1/√2 is read as 1/2.
    lexer.removeErrorListeners();
    lexer.addErrorListener(&errorListener);
    antlr4::CommonTokenStream tokens(&lexer);
    ExtendedDiracParser parser(&tokens);
    parser.removeErrorListeners();
    parser.addErrorListener(&errorListener);
    antlr4::tree::ParseTree* tree = get_tree(parser);
    return visitor->visit(tree);
}
}

#endif
