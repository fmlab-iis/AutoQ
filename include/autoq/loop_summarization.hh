
#ifndef _AUTOQ_LOOP_SUMMARIZATION_HH_
#define _AUTOQ_LOOP_SUMMARIZATION_HH_

#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/symbol/predicate.hh"
#include "autoq/symbol/index.hh"
#include "autoq/util/types.hh"
#include "autoq/aut_description.hh"
#include "autoq/util/qasm_regex.hh"

template<typename Symbol>
void execute_loop(std::vector<std::string>& loop_body, AUTOQ::Automata<Symbol>& aut, ParameterMap& params, const AUTOQ::QasmRegexes& re,
                std::smatch match_pieces, const std::vector<int>& qubit_permutation);

// std::hash for Symbol types (required by std::unordered_map; symbol headers only provide boost::hash).
namespace std {
    template<>
    struct hash<AUTOQ::Symbol::Concrete> {
        std::size_t operator()(const AUTOQ::Symbol::Concrete& symbol) const {
            return boost::hash<std::string>()(symbol.str());
        }
    };
    template<>
    struct hash<AUTOQ::Symbol::Symbolic> {
        std::size_t operator()(const AUTOQ::Symbol::Symbolic& symbol) const {
            return boost::hash<std::string>()(symbol.str());
        }
    };
}

#endif