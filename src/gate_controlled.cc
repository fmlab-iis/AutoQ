/** Controlled gate (1 or 2 controls) template. */
#include "autoq/aut_description.hh"
#include "gate_helpers.hh"
#include "gate_macros.hh"

template <typename Symbol>
void AUTOQ::Automata<Symbol>::general_controlled_gate(int c, int t, const std::function<Symbol(const Symbol&, const Symbol&)> &u1u2, const std::function<Symbol(const Symbol&, const Symbol&)> &u3u4, const std::function<Symbol(const Symbol&)> &multiply_by_c0) {
    if (c <= t) {
        THROW_AUTOQ_ERROR("We require c > t here.");
    }
    general_controlled_gate(c, c, t, u1u2, u3u4, multiply_by_c0);
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::general_controlled_gate(int c, int c2, int t, const std::function<Symbol(const Symbol&, const Symbol&)> &u1u2, const std::function<Symbol(const Symbol&, const Symbol&)> &u3u4, const std::function<Symbol(const Symbol&)> &multiply_by_c0) {
    auto minC = std::min(c, c2);
    if (minC <= t) {
        THROW_AUTOQ_ERROR("We require all c's > t here.");
    }

    AUTOQ::Automata<Symbol> result;
    gate_copy_result_base_and_check_overflow(result, *this);

    auto it = transitions.begin();
    bool it_has_been_assigned = false;
    for (auto it0 = transitions.begin(); it0 != transitions.end(); it0++) {
        if (it0->first.symbol().is_leaf()) {
            auto first = it0->first;
            first.symbol() = multiply_by_c0(first.symbol());
            for (const auto &out_ins : it0->second) {
                for (const auto &in : out_ins.second) {
                    result.transitions[first][out_ins.first].insert(in);
                }
            }
        } else if (it0->first.symbol().qubit() < t) {
            result.transitions.insert(*it0);
        } else if (!it_has_been_assigned) {
            it = it0;
            it_has_been_assigned = true;
        }
    }

    std::vector<bool> possible_next_level_states(R(stateNum-1, stateNum-1) + 1);
    assert(it->first.symbol().qubit() == t);
    for (; it != transitions.end(); it++) {
        if (it->first.is_leaf() || it->first.symbol().qubit() > t) break;
        auto &ref1 = result.transitions[it->first];
        for (const auto &out_ins : it->second) {
            auto &ref2 = ref1[out_ins.first];
            for (const auto &in : out_ins.second) {
                assert(in.size() == 2);
                ref2.insert({L(in.at(0), in.at(1)), R(in.at(0), in.at(1))});
                possible_next_level_states[L(in.at(0), in.at(1))] = true;
                possible_next_level_states[R(in.at(0), in.at(1))] = true;
            }
        }
    }

    auto head = it;
    std::map<State, std::map<Tag, std::map<Symbol, std::vector<StateVector>>>> qcfi;
    std::vector<bool> possible_previous_level_states = possible_next_level_states;
    for (; it != transitions.end(); it++) {
        if (it->first.is_leaf()) break;
        auto qubit = it->first.symbol().qubit();
        assert(qubit > t);
        if (qubit != head->first.symbol().qubit()) {
            head = it;
            possible_previous_level_states = possible_next_level_states;
        }
        for (auto it2 = head; it2 != transitions.end(); it2++) {
            if (it2->first.is_leaf()) break;
            if (it2->first.symbol().qubit() != qubit) break;
            assert(it->first.symbol() == it2->first.symbol());
            auto color_intersection = it->first.tag() & it2->first.tag();
            if (color_intersection == 0) continue;
            for (const auto &out_ins1 : it->second) {
                const auto &top1 = out_ins1.first;
                for (const auto &out_ins2 : it2->second) {
                    const auto &top2 = out_ins2.first;
                    bool qubit_is_NOT_a_control_qubit = (qubit != c) && (qubit != c2);
                    if (hasLoop || possible_previous_level_states[L(top1, top2)]) {
                        auto &ref = qcfi[L(top1, top2)][color_intersection][it->first.symbol()];
                        if (qubit_is_NOT_a_control_qubit) {
                            for (const auto &in1 : out_ins1.second) {
                                for (const auto &in2 : out_ins2.second) {
                                    ref.push_back({L(in1.at(0), in2.at(0)), L(in1.at(1), in2.at(1))});
                                }
                            }
                        } else {
                            for (const auto &in1 : out_ins1.second) {
                                for (const auto &in2 : out_ins2.second) {
                                    ref.push_back({in1.at(0), L(in1.at(1), in2.at(1))});
                                }
                            }
                        }
                    }
                    if (hasLoop || possible_previous_level_states[R(top1, top2)]) {
                        auto &ref = qcfi[R(top1, top2)][color_intersection][it->first.symbol()];
                        if (qubit_is_NOT_a_control_qubit) {
                            for (const auto &in1 : out_ins1.second) {
                                for (const auto &in2 : out_ins2.second) {
                                    ref.push_back({R(in1.at(0), in2.at(0)), R(in1.at(1), in2.at(1))});
                                }
                            }
                        } else {
                            for (const auto &in1 : out_ins1.second) {
                                for (const auto &in2 : out_ins2.second) {
                                    ref.push_back({in2.at(0), R(in1.at(1), in2.at(1))});
                                }
                            }
                        }
                    }
                }
            }
            if (qubit > minC) {
                for (const auto &out_ins : it->second) {
                    const auto &top = out_ins.first;
                    if (hasLoop || possible_previous_level_states[top]) {
                        auto &ref = qcfi[top][color_intersection][it->first.symbol()];
                        ref.insert(ref.end(), out_ins.second.begin(), out_ins.second.end());
                    }
                }
                for (const auto &out_ins : it2->second) {
                    const auto &top = out_ins.first;
                    if (hasLoop || possible_previous_level_states[top]) {
                        auto &ref = qcfi[top][color_intersection][it2->first.symbol()];
                        ref.insert(ref.end(), out_ins.second.begin(), out_ins.second.end());
                    }
                }
            }
        }
        if (std::next(it, 1) == transitions.end() || std::next(it, 1)->first.is_leaf() || qubit != std::next(it, 1)->first.symbol().qubit()) {
            flush_qcfi_to_result<Symbol>(result, qcfi, possible_next_level_states, true);
        }
    }

    head = it;
    possible_previous_level_states = possible_next_level_states;
    qcfi.clear();
    for (; it != transitions.end(); it++) {
        assert(it->first.is_leaf());
        for (auto it2 = head; it2 != transitions.end(); it2++) {
            assert(it2->first.is_leaf());
            auto color_intersection = it->first.tag() & it2->first.tag();
            if (color_intersection == 0) continue;
            for (const auto &out_ins1 : it->second) {
                const auto &top1 = out_ins1.first;
                for (const auto &out_ins2 : it2->second) {
                    const auto &top2 = out_ins2.first;
                    if (hasLoop || possible_previous_level_states[L(top1, top2)]) {
                        qcfi[L(top1, top2)][color_intersection][u1u2(it->first.symbol(), it2->first.symbol())].push_back({});
                    }
                    if (hasLoop || possible_previous_level_states[R(top1, top2)]) {
                        qcfi[R(top1, top2)][color_intersection][u3u4(it->first.symbol(), it2->first.symbol())].push_back({});
                    }
                }
            }
        }
    }
    flush_qcfi_to_result<Symbol>(result, qcfi, possible_next_level_states, false);
    result.stateNum = R(stateNum-1, stateNum-1) + 1;
    *this = result;
}

template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
