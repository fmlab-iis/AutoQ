#ifndef _AUTOQ_INCLUSION_HH_
#define _AUTOQ_INCLUSION_HH_

#include <regex>
#include <string>
#include <vector>
#include "autoq/complex/complex.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/aut_description.hh"

namespace AUTOQ {
    /// Index-inclusion implementation (used to avoid instantiating generic operator<= for Symbol=Index).
    bool inclusion_index_compare(const IndexAutomata &autA, const IndexAutomata &autB);
}

#endif