/*****************************************************************************

 *
 *  Description:
 *    Header file for abstract class of automaton format parser.
 *
 *****************************************************************************/

#ifndef _VATA_ABSTR_PARSER_HH_
#define _VATA_ABSTR_PARSER_HH_

// VATA headers
#include <vata/vata.hh>
#include <vata/util/aut_description.hh>
#include <vata/util/triple.hh>


namespace VATA
{
	namespace Parsing
	{
		class AbstrParser;
	}
}


class VATA::Parsing::AbstrParser
{
public:   // data types

	typedef VATA::Util::TreeAutomata TreeAutomata;

public:   // methods

	virtual TreeAutomata ParseString(const std::string& str) = 0;

	virtual ~AbstrParser()
	{ }
};

#endif
