/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Description:
 *    Centralized QASM regex patterns used for parsing and execution.
 *
 *****************************************************************************/

#ifndef _AUTOQ_UTIL_QASM_REGEX_HH_
#define _AUTOQ_UTIL_QASM_REGEX_HH_

#include <regex>

namespace AUTOQ {

/** Shared regex patterns for QASM parsing and execution. */
struct QasmRegexes {
    const std::regex rx;
    const std::regex rz;
    const std::regex digit;
    const std::regex loop;
    QasmRegexes()
        : rx(R"(rx\((.+)\).+\[(\d+)\];)")
        , rz(R"(rz\((.+)\).+\[(\d+)\];)")
        , digit("\\d+")
        , loop(R"(for int (\w+) in \[(\d+):(\d+)\])") {}
};

/** @deprecated Use QasmRegexes. Kept for backward compatibility. */
using regexes = QasmRegexes;

/** Regex for extracting content after "// " (e.g. loop-invariant path in while stmt). */
inline const std::regex kTrailingComment(R"(// *(.*))");

}  // namespace AUTOQ

#endif
