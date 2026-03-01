/**
 * Inclusion checking and language emptiness for tree automata.
 * This file: empty(), generic Automata<Symbol>::operator<= (→ Index), stubs, explicit instantiations.
 * See also: inclusion_index.cc, inclusion_symbolic.cc, inclusion_concrete.cc.
 */
#include "z3/z3++.h"
#include "autoq/util/util.hh"
#include "autoq/util/string.hh"
#include "autoq/inclusion.hh"
#include "autoq/aut_description.hh"
#include <queue>

template <typename Symbol>
bool AUTOQ::Automata<Symbol>::empty() const {
    std::map<State, Tag> qC; // map top to the union of all sets of colors
    std::map<State, std::map<Tag, std::map<Symbol, std::set<StateVector>>>> qcfi;
    for (const auto &t : this->transitions) {
        const SymbolTag &symbol_tag = t.first;
        for (const auto &out_ins : t.second) {
            const auto &out = out_ins.first;
            qC[out] |= symbol_tag.tag(); // union all colors for each state
            auto &ref = qcfi[out][symbol_tag.tag()][symbol_tag.symbol()];
            for (const auto &in : out_ins.second) {
                ref.insert(in);
            }
        }
    }

    typedef std::set<State> Vertex;
    std::queue<Vertex> bfs; // the queue used for traversing the graph
    for (const auto &q : this->finalStates) {
        Vertex vertex;
        vertex.insert(q);
        bfs.push(vertex);
    }
    while (!bfs.empty()) {
        Vertex vertex = bfs.front();
        bfs.pop();
        Tag range = std::numeric_limits<Tag>::max();
        for (const auto &top : vertex) {
            range &= qC[top];
        }
        Tag base = 1;
        std::vector<Tag> candidates;
        while (range) {
            if (range & 1) {
                candidates.push_back(base);
            }
            range >>= 1;
            base <<= 1;
        }
        for (auto candidate : candidates) {
            Vertex new_vertex;
            std::optional<bool> is_internal;
            bool skip_candidate = false;
            for (const auto &top : vertex) {
                bool this_top_has_picked_a_transition = false;
                for (const auto &[c, fi] : qcfi[top]) {
                    if (c & candidate) {
                        if (fi.size() != 1) THROW_AUTOQ_ERROR("The sets of choices under the top state " + std::to_string(top) + "are not disjoint!");
                        const auto &symbol = fi.begin()->first;
                        if (!is_internal.has_value()) {
                            is_internal = symbol.is_internal();
                        } else if (is_internal.value() != symbol.is_internal()) {
                            THROW_AUTOQ_ERROR("The selected transitions under this choice" + std::to_string(candidate) + "cannot be balanced!");
                        }
                        if (is_internal.value()) { // internal transitions
                            if (fi.begin()->second.size() != 1) THROW_AUTOQ_ERROR("The sets of choices under the top state " + std::to_string(top) + "are not disjoint!");
                            for (auto i : *(fi.begin()->second.begin())) {
                                new_vertex.insert(i);
                            }
                        }
                        this_top_has_picked_a_transition = true;
                        break; // only pick one transition for this top state
                    }
                }
                if (!this_top_has_picked_a_transition) { // this candidate is invalid
                    skip_candidate = true;
                    break;
                }
            }
            if (skip_candidate) continue;
            if (!is_internal.has_value()) THROW_AUTOQ_ERROR("should have picked some transitions");
            if (!is_internal.value()) return false; // if all top states have picked a leaf transition, then the language is not empty.
            if (new_vertex.empty()) THROW_AUTOQ_ERROR("Internal transitions should have some children!");
            bfs.push(new_vertex);
        }
    }
    return true; // if we can reach here, then the language is empty.
}

#include "autoq/inclusion_common.hh"

namespace {
// Helper: map symbols to indices and fill an Index automata's transitions (shared by both aut1 and aut2).
template <typename Symbol>
void migrate_transitions_to_index(
    const typename AUTOQ::Automata<Symbol>::TopDownTransitions& transitions,
    std::vector<Symbol>& symbol_map,
    AUTOQ::Automata<AUTOQ::Symbol::Index>& aut)
{
    using IndexAutomata = AUTOQ::Automata<AUTOQ::Symbol::Index>;
    for (const auto &t : transitions) {
        const auto &symbol_tag = t.first;
        const auto &symbol = symbol_tag.symbol();
        unsigned i = 0;
        for (; i <= symbol_map.size(); i++) {
            if (i == symbol_map.size()) {
                symbol_map.push_back(symbol);
            }
            bool eq;
            if constexpr (std::is_same_v<Symbol, AUTOQ::Symbol::Concrete>) {
                eq = symbol_map.at(i).valueEqual(symbol);
            } else {
                eq = symbol_map.at(i) == symbol;
            }
            if (i == symbol_map.size() || eq) {
                typename IndexAutomata::SymbolTag symbol_tag2{AUTOQ::Symbol::Index(symbol.is_leaf(), i), symbol_tag.tag()};
                for (const auto &out_ins : t.second) {
                    const auto &out = out_ins.first;
                    const auto &ins = out_ins.second;
                    for (const auto &in : ins) {
                        aut.transitions[symbol_tag2][out].insert(in);
                    }
                }
                break;
            }
        }
    }
}
}  // namespace

// -------- Inclusion: generic Automata<Symbol> (convert to Index then compare) --------
template <typename Symbol>
bool AUTOQ::Automata<Symbol>::operator<=(const Automata<Symbol> &autB) const {
    if constexpr (std::is_same_v<Symbol, AUTOQ::Symbol::Index>) {
        return inclusion_index_compare(*this, static_cast<const IndexAutomata &>(autB));
    }
    // migrate instance variables
    Automata<AUTOQ::Symbol::Index> aut1;
    aut1.name = this->name;
    aut1.finalStates = this->finalStates;
    aut1.stateNum = this->stateNum;
    aut1.qubitNum = this->qubitNum;
    aut1.isTopdownDeterministic = this->isTopdownDeterministic;
    Automata<AUTOQ::Symbol::Index> aut2;
    aut2.name = autB.name;
    aut2.finalStates = autB.finalStates;
    aut2.stateNum = autB.stateNum;
    aut2.qubitNum = autB.qubitNum;
    aut2.isTopdownDeterministic = autB.isTopdownDeterministic;
    aut2.set_execution_stats(this->execution_stats());
    // migrate transitions (shared symbol_map for both automata)
    std::vector<Symbol> symbol_map;
    migrate_transitions_to_index<Symbol>(this->transitions, symbol_map, aut1);
    migrate_transitions_to_index<Symbol>(autB.transitions, symbol_map, aut2);
    // main routine
    bool result = aut1 <= aut2;
    // aut1 and aut2 shared stats_ during check, no copy back needed
    return result;
}

// (Symbolic inclusion: check_validity, scaled_inclusion, SymbolicAutomata::operator<<= in inclusion_symbolic.cc)
// (ConcreteAutomata::operator<<= in inclusion_concrete.cc)

template <>
bool AUTOQ::PredicateAutomata::operator<<=(AUTOQ::PredicateAutomata) const {
    THROW_AUTOQ_ERROR("PredicateAutomata::operator<<= not implemented");
}
template <>
bool AUTOQ::IndexAutomata::operator<<=(AUTOQ::IndexAutomata) const {
    THROW_AUTOQ_ERROR("IndexAutomata::operator<<= not implemented");
}
template <>
bool AUTOQ::ConstrainedAutomata::operator<<=(AUTOQ::ConstrainedAutomata) const {
    THROW_AUTOQ_ERROR("ConstrainedAutomata::operator<<= not implemented");
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Predicate>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Index>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Constrained>;