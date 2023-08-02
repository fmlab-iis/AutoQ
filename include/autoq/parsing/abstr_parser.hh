/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Copyright (c) 2011  Ondra Lengal <ilengal@fit.vutbr.cz>
 *
 *  Description:
 *    Header file for abstract class of automaton format parser.
 *
 *****************************************************************************/

#ifndef _AUTOQ_ABSTR_PARSER_HH_
#define _AUTOQ_ABSTR_PARSER_HH_

// AUTOQ headers
#include <autoq/autoq.hh>
#include <autoq/aut_description.hh>
#include <autoq/util/triple.hh>


namespace AUTOQ
{
	namespace Parsing
	{
		class AbstrParser;
	}
}


class AUTOQ::Parsing::AbstrParser
{
public:   // data types

	typedef AUTOQ::TreeAutomata TreeAutomata;

public:   // methods

	virtual TreeAutomata ParseString(const std::string& str) = 0;

	virtual ~AbstrParser()
	{ }
};

#endif
