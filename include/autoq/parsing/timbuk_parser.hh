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
#include <autoq/parsing/abstr_parser.hh>
#include <autoq/util/convert.hh>
#include <autoq/util/triple.hh>
#include <autoq/util/aut_description.hh>

namespace AUTOQ
{
	namespace Parsing
	{
		template <typename InitialSymbol>
        class TimbukParser;
	}
}


/**
 * @brief  Class for a parser of automata in the Timbuk format
 *
 * This class is a parser for automata in the Timbuk format.
 */
template <typename InitialSymbol>
class AUTOQ::Parsing::TimbukParser //:
	// public AUTOQ::Parsing::AbstrParser
{
public:   // methods

	/**
	 * @copydoc  AUTOQ::Parsing::AbstrParser::ParseString
	 */
	static AUTOQ::Util::Automata<InitialSymbol> ParseString(const std::string& str);
    static AUTOQ::Util::Automata<InitialSymbol> FromFileToAutomata(const char* filepath);
    static AUTOQ::Util::Automata<InitialSymbol> from_tree_to_automaton(std::string tree);
    static AUTOQ::Util::Automata<InitialSymbol> from_line_to_automaton(std::string line);

	/**
	 * @copydoc  AUTOQ::Parsing::AbstrParser::~AbstrParser
	 */
	virtual ~TimbukParser()
	{ }

private:
    // Disallow creating an instance of this object
    TimbukParser() {}
};

#endif
