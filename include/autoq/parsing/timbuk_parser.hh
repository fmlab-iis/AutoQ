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
#include <autoq/autoq.hh>
#include <autoq/util/convert.hh>
#include <autoq/util/triple.hh>
#include <autoq/aut_description.hh>

namespace AUTOQ
{
	namespace Parsing
	{
		template <typename Symbol>
        class TimbukParser;
	}
}


/**
 * @brief  Class for a parser of automata in the Timbuk format
 *
 * This class is a parser for automata in the Timbuk format.
 */
template <typename Symbol>
class AUTOQ::Parsing::TimbukParser
{
public:   // methods
    static AUTOQ::Automata<Symbol> ReadAutomaton(const std::string& filepath);
    static AUTOQ::Automata<Symbol> ReadAutomatonAndConstraint(const std::string& filepath, std::string& constraint);
    static AUTOQ::Automata<Symbol> parse_hsl_from_istream(std::istream *is);

private:
    // Disallow creating an instance of this object
    TimbukParser() {}
    static AUTOQ::Automata<Symbol> from_tree_to_automaton(std::string tree);
    static AUTOQ::Automata<Symbol> from_line_to_automaton(std::string line);
};

#endif
