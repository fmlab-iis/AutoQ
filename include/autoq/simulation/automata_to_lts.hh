/**
 * LTS construction from tree automata: build ExplicitLTS from Automata for simulation.
 * - translate_to_lts_downward: one-way translation automaton -> LTS.
 * - count_aut_states: number of distinct states (used for LTS size).
 */
#ifndef AUTOQ_SIMULATION_AUTOMATA_TO_LTS_HH
#define AUTOQ_SIMULATION_AUTOMATA_TO_LTS_HH

#include <unordered_map>
#include <set>

#include "autoq/aut_description.hh"
#include "autoq/simulation/explicit_lts.hh"
#include "autoq/simulation/transl_weak.hh"

namespace AUTOQ {
namespace simulation {

template <class Index, typename Symbol>
ExplicitLTS translate_to_lts_downward(
    const Automata<Symbol>& aut,
    size_t numStates,
    Index& stateIndex)
{
    using State = typename Automata<Symbol>::State;
    using SymbolTag = typename Automata<Symbol>::SymbolTag;
    using StateVector = typename Automata<Symbol>::StateVector;

    std::unordered_map<SymbolTag, size_t> symbolMap;
    std::unordered_map<const StateVector*, size_t> lhsMap;

    size_t symbolCnt = 0;
    Util::TranslatorWeak2<std::unordered_map<SymbolTag, size_t>>
        symbolTranslator(symbolMap, [&symbolCnt](const SymbolTag&) { return symbolCnt++; });

    size_t lhsCnt = numStates;
    Util::TranslatorWeak2<std::unordered_map<const StateVector*, size_t>>
        lhsTranslator(lhsMap, [&lhsCnt](const StateVector*) { return lhsCnt++; });

    ExplicitLTS result(numStates);

    for (const State& finState : aut.finalStates) {
        stateIndex[finState];
    }

    for (const auto& symMap : aut.transitions) {
        const auto& symbolName = symbolTranslator(symMap.first);

        for (const auto& vecSet : symMap.second) {
            const auto& parent = vecSet.first;

            for (const auto& tuple : vecSet.second) {
                const auto& parentName = stateIndex[parent];

                size_t dest;
                if (1 == tuple.size()) {
                    dest = stateIndex[tuple.front()];
                    assert(dest < numStates);
                } else {
                    dest = lhsTranslator(&tuple);
                }

                result.addTransition(parentName, symbolName, dest);
            }
        }
    }

    for (auto& tupleIndexPair : lhsMap) {
        assert(tupleIndexPair.first);

        size_t i = 0;
        for (auto& state : *tupleIndexPair.first) {
            size_t dest = stateIndex[state];
            assert(dest < numStates);

            result.addTransition(tupleIndexPair.second, symbolMap.size() + i, dest);
            ++i;
        }
    }

    result.init();

    return result;
}

template <typename Symbol>
size_t count_aut_states(const Automata<Symbol>& aut)
{
    using State = typename Automata<Symbol>::State;

    std::set<State> states;
    for (const auto& state : aut.finalStates) {
        states.insert(state);
    }

    for (const auto& symMap : aut.transitions) {
        for (const auto& out_ins : symMap.second) {
            states.insert(out_ins.first);
            for (const auto& in : out_ins.second) {
                for (const auto& child : in)
                    states.insert(child);
            }
        }
    }

    return states.size();
}

}  // namespace simulation
}  // namespace AUTOQ

#endif
