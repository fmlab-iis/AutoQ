// Implementation of parameter map

#ifndef AUTOQ_UTIL_TYPES_HH
#define AUTOQ_UTIL_TYPES_HH

#include <unordered_map>
#include <string>
#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/symbol/predicate.hh"
#include "autoq/symbol/index.hh"

using ParameterMap = std::unordered_map<std::string, std::string>;
using SymbolicMap = std::unordered_map<AUTOQ::Symbol::Symbolic, AUTOQ::Symbol::Symbolic>; // Symbolic to Symbolic

template<typename Symbol>
using AbstractionMap = std::unordered_map<Symbol, AUTOQ::Symbol::Symbolic>; // Concrete to Symbolic

#endif // AUTOQ_UTIL_TYPES_HH