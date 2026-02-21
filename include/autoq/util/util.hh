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

#include <string>
#include <vector>
#include <chrono>

// AUTOQ headers
#include "autoq/error.hh"

namespace AUTOQ
{
	namespace Util
	{
		std::string ReadFile(const std::string& fileName);
        std::string ShellCmd(const std::string &cmd);
        #if 0
        std::string ShellCmd(const std::vector<std::string> &cmd);
        #endif
        std::string print_duration(const std::chrono::steady_clock::duration &tp);
        size_t getPeakRSS();
        size_t getCurrentRSS();

		/** User-visible output: stdout for normal messages, stderr for errors. */
		namespace Log {
			void info(const std::string& msg);
			void error(const std::string& msg);
		}
	}
}

#endif
