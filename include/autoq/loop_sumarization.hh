
#ifndef _AUTOQ_LOOP_SUMARIZATION_HH_
#define _AUTOQ_LOOP_SUMARIZATION_HH_

#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/symbol/predicate.hh"
#include "autoq/symbol/index.hh"
#include "autoq/util/types.hh"
#include "autoq/aut_description.hh"

template<typename Symbol>
void execute_loop(const std::vector<std::string>& loop_body, AUTOQ::Automata<Symbol>& aut, ParameterMap& params);


#endif