/** Shared helpers for gate implementations. Include after aut_description.hh (and util.hh for concrete_gate_finish). */
#ifndef AUTOQ_GATE_HELPERS_HH
#define AUTOQ_GATE_HELPERS_HH

#include <chrono>
#include <iostream>
#include "autoq/util/util.hh"

namespace {
/// After a concrete gate body: record duration, gateCount++, total_gate_time, and optional gateLog line.
template <typename Symbol>
void concrete_gate_finish(AUTOQ::Automata<Symbol>& self, const char* name, int t,
    std::chrono::steady_clock::time_point start) {
    auto duration = std::chrono::steady_clock::now() - start;
    self.stats_->gateCount++;
    self.stats_->total_gate_time += duration;
    if (self.stats_->gateLog)
        std::cout << name << t << "：" << self.stateNum << " states " << self.count_transitions()
                  << " transitions " << AUTOQ::Util::print_duration(duration) << "\n";
}

/// Copy result base fields from src and check state-number overflow for product-shaped expansion.
template <typename Symbol>
void gate_copy_result_base_and_check_overflow(
    AUTOQ::Automata<Symbol>& result,
    const AUTOQ::Automata<Symbol>& src)
{
    using State = typename AUTOQ::Automata<Symbol>::State;
    result.name = src.name;
    result.qubitNum = src.qubitNum;
    result.isTopdownDeterministic = src.isTopdownDeterministic;
    result.finalStates = src.finalStates;
    result.hasLoop = src.hasLoop;
    result.vars = src.vars;
    result.constraints = src.constraints;
    bool overflow = (src.stateNum > (std::numeric_limits<State>::max() - src.stateNum) / src.stateNum / 2);
    if (overflow)
        THROW_AUTOQ_ERROR("The number of states after multiplication is too large.");
}

template <typename Symbol>
void flush_qcfi_to_result(
    AUTOQ::Automata<Symbol>& result,
    std::map<typename AUTOQ::Automata<Symbol>::State, std::map<typename AUTOQ::Automata<Symbol>::Tag, std::map<Symbol, std::vector<typename AUTOQ::Automata<Symbol>::StateVector>>>>& qcfi,
    std::vector<bool>& possible_next_level_states,
    bool update_possible_states = true)
{
    for (const auto &q_ : qcfi) {
        for (const auto &c_ : q_.second) {
            for (const auto &f_ : c_.second) {
                result.transitions[{f_.first, c_.first}][q_.first].insert(f_.second.begin(), f_.second.end());
                if (update_possible_states) {
                    for (const auto &i : f_.second) {
                        for (const auto &s : i)
                            possible_next_level_states[s] = true;
                    }
                }
            }
        }
    }
    qcfi.clear();
}
}  // namespace

#endif
