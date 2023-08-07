/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Copyright (c) 2011  Ondra Lengal <ilengal@fit.vutbr.cz>
 *
 *  Description:
 *    Header file for a serializer of automata to Timbuk format.
 *
 *****************************************************************************/

#ifndef _AUTOQ_TIMBUK_SERIALIZER_HH_
#define _AUTOQ_TIMBUK_SERIALIZER_HH_

// AUTOQ headers
#include <autoq/autoq.hh>
#include <autoq/serialization/abstr_serializer.hh>

namespace AUTOQ
{
	namespace Serialization
	{
		class TimbukSerializer;
	}
}

/**
 * @brief  Class for a serializer of automata into the Timbuk format
 *
 * This class is a serializer of automata into the Timbuk format.
 */
class AUTOQ::Serialization::TimbukSerializer //:
	// public AUTOQ::Serialization::AbstrSerializer
{
public:   // data types

private:  // data members

	// std::string name_;
    TimbukSerializer() {}

public:   // methods

	// TimbukSerializer() :
	// 	name_("anonymous")
	// { }

	// inline void SetName(const std::string& name)
	// {
	// 	name_ = name;
	// }

	template <typename Symbol>
    static std::string Serialize(AUTOQ::Automata<Symbol> desc);
};

#endif
