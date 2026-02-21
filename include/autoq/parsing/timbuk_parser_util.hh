/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Description:
 *    Utility functions used by the Timbuk parser (loop-invariant file discovery).
 *****************************************************************************/

#ifndef AUTOQ_PARSING_TIMBUK_PARSER_UTIL_HH
#define AUTOQ_PARSING_TIMBUK_PARSER_UTIL_HH

#include <string>
#include <vector>

namespace AUTOQ {
namespace Parsing {

std::vector<std::string> find_all_loop_invariants(const char* filename);

}  // namespace Parsing
}  // namespace AUTOQ

#endif
