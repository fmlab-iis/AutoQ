
#ifndef _AUTOQ_LOOP_SUMARIZATION_HH_
#define _AUTOQ_LOOP_SUMARIZATION_HH_

#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/symbol/predicate.hh"
#include "autoq/symbol/index.hh"
#include "autoq/util/types.hh"
#include "autoq/aut_description.hh"

template<typename Symbol>
void execute_loop(std::vector<std::string>& loop_body, AUTOQ::Automata<Symbol>& aut, ParameterMap& params, const AUTOQ::regexes& regexes,
                const std::sregex_iterator& END, std::smatch match_pieces);

template<typename Symbol>
AUTOQ::Automata<Symbol> symbolic_loop(const std::vector<std::string>& loop_body, AUTOQ::Automata<Symbol>& aut, const AUTOQ::regexes& regexes);

template<typename Symbol>
AUTOQ::Automata<AUTOQ::Symbol::Symbolic> initial_abstraction(AUTOQ::Automata<Symbol>& aut, InverseAbstractionMap<Symbol>& inverse_alpha);

namespace std{

    template<>
    struct hash<AUTOQ::Symbol::Concrete> {
        std::size_t operator()(const AUTOQ::Symbol::Concrete symbol) const {
            return boost::hash<std::string>()(symbol.str());
        }
    };
    template<>
    struct hash<AUTOQ::Symbol::Symbolic> {
        std::size_t operator()(const AUTOQ::Symbol::Symbolic symbol) const {
            return boost::hash<std::string>()(symbol.str());
        }
    };

}

#endif