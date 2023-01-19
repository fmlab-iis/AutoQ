/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Copyright (c) 2011  Ondra Lengal <ilengal@fit.vutbr.cz>
 *
 *  Description:
 *    Header file for abstract serialization class.
 *
 *****************************************************************************/

#ifndef _AUTOQ_ABSTR_SERIALIZER_HH_
#define _AUTOQ_ABSTR_SERIALIZER_HH_

// AUTOQ headers
#include <autoq/autoq.hh>
#include <autoq/util/aut_description.hh>


namespace AUTOQ
{
	namespace Serialization
	{
		class AbstrSerializer;
	}
}


class AUTOQ::Serialization::AbstrSerializer
{
public:   // data types

	typedef AUTOQ::Util::TreeAutomata TreeAutomata;

public:   // methods

	virtual std::string Serialize(const TreeAutomata& desc) = 0;

	virtual ~AbstrSerializer()
	{ }
};


#endif
