#ifndef _AUTOQ_SYMBOL_HASH_HH_
#define _AUTOQ_SYMBOL_HASH_HH_

/// std::hash for Symbol types (required by std::unordered_map; symbol headers only provide boost::hash).
#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include <string>

namespace std {
template <>
struct hash<AUTOQ::Symbol::Concrete> {
    std::size_t operator()(const AUTOQ::Symbol::Concrete& symbol) const {
        return boost::hash<std::string>()(symbol.str());
    }
};
template <>
struct hash<AUTOQ::Symbol::Symbolic> {
    std::size_t operator()(const AUTOQ::Symbol::Symbolic& symbol) const {
        return boost::hash<std::string>()(symbol.str());
    }
};
}  // namespace std

#endif
