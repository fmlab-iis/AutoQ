/*****************************************************************************
 *  AUTOQ Timbuk parser – shared utilities (declarations).
 *
 *  String/file helpers and Constants-section helpers used when loading
 *  automata. Definitions: strip_line_comments, split_automaton_and_constraints,
 *  find_all_loop_invariants in timbuk_parser_util.cc; parse_constants_section,
 *  unify_complex_k in timbuk_parser_grammar.cc.
 *
 *  Main functions: strip_line_comments(), split_automaton_and_constraints(),
 *  find_all_loop_invariants(), parse_constants_section(), unify_complex_k().
 *****************************************************************************/

#ifndef AUTOQ_PARSING_TIMBUK_PARSER_UTIL_HH
#define AUTOQ_PARSING_TIMBUK_PARSER_UTIL_HH

#include <map>
#include <string>
#include <utility>
#include <vector>

#include "autoq/complex/complex.hh"

namespace AUTOQ {
namespace Parsing {

void strip_line_comments(std::string& s);
std::pair<std::string, std::string> split_automaton_and_constraints(const std::string& fileContents);
std::vector<std::string> find_all_loop_invariants(const char* filename);
void parse_constants_section(std::string& fileContents,
                             std::map<std::string, AUTOQ::Complex::Complex>& out_constants);
void unify_complex_k(std::map<std::string, AUTOQ::Complex::Complex>& constants);

}  // namespace Parsing
}  // namespace AUTOQ

#endif
