/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Copyright (c) 2011  Ondra Lengal <ilengal@fit.vutbr.cz>
 *
 *  Description:
 *    Header file for miscellaneous utility gadgets.
 *
 *****************************************************************************/

#ifndef _AUTOQ_STRING_HH_
#define _AUTOQ_STRING_HH_

#include <string>
#include <vector>

namespace AUTOQ
{
	namespace String
	{
        std::string trim(const std::string& str);
        std::vector<std::string> split_delim(const std::string &str, char delim);
        std::string read_word(std::string& str);
        bool contains_whitespace(const std::string& str);
        std::pair<std::string, int> parse_colonned_token(std::string str);
	}
}

#endif
