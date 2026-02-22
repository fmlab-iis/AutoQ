#ifndef _AUTOQ_INCLUSION_BUILD_TRANS_HH_
#define _AUTOQ_INCLUSION_BUILD_TRANS_HH_

#include "autoq/aut_description.hh"
#include <vector>
#include <map>

namespace AUTOQ {

/// Builds transA and transB from two automata for inclusion BFS (shared by Index, Concrete, Symbolic).
/// transA[out][symbol_tag] = single StateVector; transB[out][symbol][tag] = StateVector.
template <typename Symbol>
void build_inclusion_trans(
    const Automata<Symbol>& autA,
    const Automata<Symbol>& autB,
    std::vector<std::map<typename Automata<Symbol>::SymbolTag, typename Automata<Symbol>::StateVector>>& transA,
    std::vector<std::map<typename Automata<Symbol>::Symbol, std::map<typename Automata<Symbol>::Tag, typename Automata<Symbol>::StateVector>>>& transB)
{
    transA.resize(autA.stateNum);
    transB.resize(autB.stateNum);
    for (const auto &t : autA.transitions) {
        const auto &symbol_tag = t.first;
        for (const auto &out_ins : t.second) {
            const auto &out = out_ins.first;
            const auto &ins = out_ins.second;
            assert(ins.size() == 1);
            transA[out][symbol_tag] = *(ins.begin());
        }
    }
    for (const auto &t : autB.transitions) {
        const auto &symbol_tag = t.first;
        for (const auto &out_ins : t.second) {
            const auto &out = out_ins.first;
            const auto &ins = out_ins.second;
            assert(ins.size() == 1);
            transB[out][symbol_tag.symbol()][symbol_tag.tag()] = *(ins.begin());
        }
    }
}

}  // namespace AUTOQ

#endif
