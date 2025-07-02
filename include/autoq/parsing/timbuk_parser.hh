/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Copyright (c) 2011  Ondra Lengal <ilengal@fit.vutbr.cz>
 *
 *  Description:
 *    Parser of Timbuk format.
 *
 *****************************************************************************/

#ifndef _AUTOQ_TIMBUK_PARSER_HH_
#define _AUTOQ_TIMBUK_PARSER_HH_

// AUTOQ headers
#include "autoq/aut_description.hh"
#include "autoq/complex/complex.hh"
#include <variant>

namespace AUTOQ
{
	namespace Parsing
	{
		template <typename Symbol>
        struct TimbukParser;
	}
}


/**
 * @brief  Class for a parser of automata in the Timbuk format
 *
 * This class is a parser for automata in the Timbuk format.
 */
template <typename Symbol>
struct AUTOQ::Parsing::TimbukParser
{
    // static AUTOQ::Automata<Symbol> ParseString(std::string fileContents);
    static AUTOQ::Automata<Symbol> ReadAutomaton(const std::string& filepath);
    static std::tuple<AUTOQ::Automata<Symbol>, AUTOQ::Automata<Symbol>, std::vector<int>> ReadTwoAutomata(const std::string& filepath1, const std::string& filepath2);
    static AUTOQ::Automata<Symbol> ReadAutomaton(const std::string& filepath, bool &do_not_throw_term_undefined_error);
    static std::tuple<AUTOQ::Automata<Symbol>, AUTOQ::Automata<Symbol>, std::vector<int>> ReadTwoAutomata(const std::string& filepath1, const std::string& filepath2, bool &do_not_throw_term_undefined_error);
    static AUTOQ::Automata<Symbol> parse_extended_dirac_from_istream(std::istream *is, bool &do_not_throw_term_undefined_error, const std::map<std::string, AUTOQ::Complex::Complex> &constants = {}, const std::map<std::string, std::string> &predicates = {});
    static std::tuple<AUTOQ::Automata<Symbol>, AUTOQ::Automata<Symbol>, std::vector<int>> parse_two_extended_diracs_from_istream(std::istream *is1, std::istream *is2, bool &do_not_throw_term_undefined_error, const std::map<std::string, AUTOQ::Complex::Complex> &constants1 = {}, const std::map<std::string, std::string> &predicates1 = {}, const std::map<std::string, AUTOQ::Complex::Complex> &constants2 = {}, const std::map<std::string, std::string> &predicates2 = {});
};

std::variant<AUTOQ::Automata<AUTOQ::Symbol::Concrete>, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>, AUTOQ::Automata<AUTOQ::Symbol::Predicate>> ReadAutomaton(const std::string& filepath);

#endif
