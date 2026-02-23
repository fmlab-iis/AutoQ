/** Diagonal gate template. */
#include "autoq/aut_description.hh"
#include "gate_macros.hh"

template <typename Symbol>
void AUTOQ::Automata<Symbol>::diagonal_gate(int t, const std::function<void(Symbol*)> &multiply_by_c0, const std::function<void(Symbol*)> &multiply_by_c1) {
    TopDownTransitions transitions2;
    std::map<State, int> topStateIsLeftOrRight, childStateIsLeftOrRight;

    InternalTopDownTransitions internalTransitions(qubitNum + 1 + (hasLoop ? 1 : 0));
    TopDownTransitions leafTransitions;
    for (const auto &tr : transitions) {
        if (tr.first.is_internal()) {
            if (tr.first.symbol().qubit() < t)
                transitions2[tr.first] = tr.second;
            else
                internalTransitions[static_cast<int>(tr.first.symbol().qubit())][tr.first.tag()] = tr.second;
        } else {
            leafTransitions[tr.first] = tr.second;
        }
    }

    for (int q = t; q <= qubitNum + (hasLoop ? 1 : 0); q++) {
        if (q == t) {
            for (const auto &tag_outins : internalTransitions[q]) {
                for (const auto &out_ins : tag_outins.second) {
                    for (const auto &in : out_ins.second) {
                        assert(in.size() == 2);
                        childStateIsLeftOrRight[in[0]] |= 0b10;
                        childStateIsLeftOrRight[in[1]] |= 0b01;
                    }
                }
            }
            for (const auto &tag_outins : internalTransitions[q]) {
                auto &ref = transitions2[{Symbol(q), tag_outins.first}];
                for (const auto &out_ins : tag_outins.second) {
                    const auto &top = out_ins.first;
                    auto &reftop = ref[top];
                    for (const auto &in : out_ins.second) {
                        assert(in.size() == 2);
                        queryChildID(in[1], newIn1);
                        reftop.insert({in[0], newIn1});
                    }
                }
            }
        } else {
            for (const auto &tag_outins : internalTransitions[q]) {
                for (const auto &out_ins : tag_outins.second) {
                    const auto &top = out_ins.first;
                    auto val = topStateIsLeftOrRight[top];
                    for (const auto &in : out_ins.second) {
                        assert(in.size() == 2);
                        childStateIsLeftOrRight[in[0]] |= val;
                        childStateIsLeftOrRight[in[1]] |= val;
                    }
                }
            }
            for (const auto &tag_outins : internalTransitions[q]) {
                auto &ref = transitions2[{Symbol(q), tag_outins.first}];
                for (const auto &out_ins : tag_outins.second) {
                    const auto &top = out_ins.first;
                    auto val = topStateIsLeftOrRight[top];
                    if (val & 0b10) {
                        ref[top] = out_ins.second;
                    }
                    queryTopID(top, newTop);
                    auto &refnewTop = ref[newTop];
                    if (val & 0b01) {
                        for (const auto &in : out_ins.second) {
                            assert(in.size() == 2);
                            queryChildID(in[0], newIn0);
                            queryChildID(in[1], newIn1);
                            refnewTop.insert({newIn0, newIn1});
                        }
                    }
                }
            }
        }
        topStateIsLeftOrRight = childStateIsLeftOrRight;
        childStateIsLeftOrRight.clear();
    }
    for (const auto &tr : leafTransitions) {
        for (const auto &out_ins : tr.second) {
            const auto &top = out_ins.first;
            auto val = topStateIsLeftOrRight[top];
            if (val & 0b10) {
                SymbolTag symbol_tag = tr.first;
                multiply_by_c0(&symbol_tag.symbol());
                transitions2[symbol_tag][top].insert({{}});
            }
            if (val & 0b01) {
                SymbolTag symbol_tag = tr.first;
                multiply_by_c1(&symbol_tag.symbol());
                queryTopID(top, newTop);
                transitions2[symbol_tag][newTop].insert({{}});
            }
        }
    }
    transitions = transitions2;
    stateNum *= 2;
}

template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
