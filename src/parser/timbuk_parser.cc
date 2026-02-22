/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Copyright (c) 2011  Ondra Lengal <ilengal@fit.vutbr.cz>
 *
 *  Description:
 *    The source code for the parser of Timbuk format.
 *
 *****************************************************************************/

// C++ headers
#include <regex>
#include <fstream>
#include <numeric>
#include <filesystem>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wold-style-cast"
#include <boost/algorithm/string/predicate.hpp>
#pragma GCC diagnostic pop

// AUTOQ headers
#include "autoq/error.hh"
#include "autoq/util/util.hh"
#include "autoq/util/string.hh"
#include "autoq/aut_description.hh"
#include "autoq/complex/complex.hh"
#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/symbol/predicate.hh"
#include "autoq/parsing/parser/timbuk_parser.hh"
#include "autoq/parsing/parser/timbuk_parser_util.hh"
#include "autoq/parsing/complex_parser.hh"
#include "autoq/complex/symbolic_complex.hh"
#include "autoq/parsing/symboliccomplex_parser.hh"
#include "autoq/parsing/constraint_parser.hh"

// ANTLR4 headers
#include "autoq/parsing/ExtendedDirac/EvaluationVisitor.h"

#include "autoq/parsing/parser/timbuk_parser_grammar.hh"
#include "autoq/parsing/parser/timbuk_parser_transitions.hh"
#include "autoq/parsing/parser/timbuk_parser_dirac.hh"
#include "autoq/parsing/parser/timbuk_parser_loader.hh"

std::variant<AUTOQ::Automata<AUTOQ::Symbol::Concrete>, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>, AUTOQ::Automata<AUTOQ::Symbol::Predicate>> ReadAutomaton(const std::string& filepath) {
    std::string fileContents = AUTOQ::Util::ReadFile(filepath);
    if (fileContents.find("Predicates") != std::string::npos) {
        return AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>::ReadAutomaton(filepath);
    } else {
        bool encountered_undefined = false;
        auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(filepath, false, &encountered_undefined);
        if (!encountered_undefined)
            return aut;
        return AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadAutomaton(filepath);
    }
}

std::variant<AUTOQ::Automata<AUTOQ::Symbol::Concrete>, AUTOQ::Automata<AUTOQ::Symbol::Predicate>> ReadPossiblyPredicateAutomaton(const std::string& filepath) {
    std::string fileContents = AUTOQ::Util::ReadFile(filepath);
    bool encountered_undefined = false;
    auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(filepath, false, &encountered_undefined);
    if (!encountered_undefined)
        return aut;
    return AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>::ReadAutomaton(filepath);
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>;
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>;
template struct AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic, AUTOQ::Symbol::Predicate>;
