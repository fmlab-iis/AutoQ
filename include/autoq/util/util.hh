/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Copyright (c) 2011  Ondra Lengal <ilengal@fit.vutbr.cz>
 *
 *  Description:
 *    Header file for miscellaneous utility gadgets.
 *
 *****************************************************************************/

#ifndef _AUTOQ_UTIL_HH_
#define _AUTOQ_UTIL_HH_

#include <vector>
#include <chrono>

// AUTOQ headers
#include "autoq/autoq.hh"
// #include "autoq/aut_base.hh"

namespace AUTOQ
{
	namespace Util
	{
		std::string ReadFile(const std::string& fileName);
        bool ShellCmd(const std::string &cmd, std::string &result);
        #if 0
        bool ShellCmd(const std::vector<std::string> &cmd, std::string &result);
        #endif
        std::string trim(const std::string& str);
        std::string print_duration(const std::chrono::steady_clock::duration &tp);
	}
}

#endif
