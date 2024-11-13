#include "autoq/aut_description.hh"
#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/symbol/predicate.hh"
#include <numeric> // used in std::numeric_limits
#include <chrono> // used in remove_useless
#include <queue> // used in remove_useless

template <typename Symbol>
AUTOQ::Automata<Symbol> AUTOQ::Automata<Symbol>::operator*(Automata<Symbol> aut2) const {
    // Step 1. Modify the first-layer transitions of aut2 so that
    //         (1) there is only one root state, and
    //         (2) all colors in these transitions are disjoint.
    // But notice that we actually do not modify root states here
    // since these states will become the leaf states of aut1 eventually.
    // That is, we only modify the colors here.
    // One way is to simply recolor all these transitions such that
    // each color set uses only 1 bit.
    TopDownTransitions aut2_transitions_at_1st_layer;
    AUTOQ::Automata<Symbol>::Tag color = 1;
    int num_of_colors_used_in_aut2 = 0;
    for (auto it = aut2.transitions.cbegin(); it != aut2.transitions.cend() /* not hoisted */; /* no increment */) {
        if (it->first.is_internal() && it->first.symbol().qubit() == 1) {
            if (color == AUTOQ::Automata<Symbol>::Tag_MAX) {
                THROW_AUTOQ_ERROR("Colors are not enough!!!");
            }
            for (const auto &out_ins : it->second) {
                auto out = out_ins.first;
                for (const auto &in : out_ins.second) {
                    aut2_transitions_at_1st_layer[AUTOQ::Automata<Symbol>::SymbolTag(it->first.symbol(), AUTOQ::Automata<Symbol>::Tag(color))][out].insert(in);
                    num_of_colors_used_in_aut2++;
                    color <<= 1;
                }
            }
            aut2.transitions.erase(it++);    // or "it = aut2.transitions.erase(it)" since C++11
            // https://stackoverflow.com/a/8234813/11550178
        } else {
            ++it;
        }
    }
    for (const auto &t : aut2_transitions_at_1st_layer) {
        aut2.transitions[t.first] = t.second;
    }
    // Now "num_of_colors_used_in_aut2" denotes the number of bits for colors in aut2.

    // Step 2. For each leaf transition of aut1, we construct one "state-disjoint" copy of aut2,
    //         (1) whose root states are replaced with the top state of that leaf transition, and
    //         (2) whose colors of the first-layer transitions are prepended with the color of that leaf transition, and
    //         (3) whose leaf symbols are multiplied with the symbol of that leaf transition, and
    //         (4) finally we remove that leaf transition.
    auto aut = *this;
    TopDownTransitions transitions_to_be_appended;
    for (auto it = aut.transitions.cbegin(); it != aut.transitions.cend() /* not hoisted */; /* no increment */) {
        if (it->first.is_leaf()) {
            for (const auto &out_ins : it->second) {
                auto the_top_state_of_that_leaf_transition = out_ins.first; // (1)
                assert(out_ins.second == std::set<StateVector>({{}}));
                auto the_color_of_that_leaf_transition = it->first.tag(); // (2)
                int num_of_colors_used_in_that_leaf_transition = 0;
                auto tmp = the_color_of_that_leaf_transition;
                while (tmp > 0) {
                    num_of_colors_used_in_that_leaf_transition++;
                    tmp >>= 1;
                }
                if (num_of_colors_used_in_that_leaf_transition * num_of_colors_used_in_aut2 > std::numeric_limits<Tag>::digits) {
                    THROW_AUTOQ_ERROR("The shifted color is out of range!!!");
                }
                for (const auto &t : aut2.transitions) {
                    if (t.first.is_leaf()) { // (3)
                        auto &ref = transitions_to_be_appended[AUTOQ::Automata<Symbol>::SymbolTag(it->first.symbol() * t.first.symbol(), t.first.tag())];
                        for (const auto &out_ins : t.second) {
                            auto out = out_ins.first;
                            out += aut.stateNum;
                            auto &container = ref[out];
                            for (auto in : out_ins.second) {
                                for (unsigned i=0; i<in.size(); i++) {
                                    in[i] += aut.stateNum;
                                }
                                container.insert(in);
                            }
                        }
                    } else if (t.first.symbol().qubit() == 1) { // (1)(2)
                        int counter = 0;
                        Tag new_color_pair = 0;
                        auto tmpi = the_color_of_that_leaf_transition;
                        for (int i=0; i<num_of_colors_used_in_that_leaf_transition; i++) {
                            auto tmpj = t.first.tag();
                            for (int j=0; j<num_of_colors_used_in_aut2; j++) {
                                if (tmpi & tmpj & 1)
                                    new_color_pair |= static_cast<Tag>(1) << counter;
                                counter++;
                                tmpj >>= 1;
                            }
                            tmpi >>= 1;
                        }
                        auto &ref = transitions_to_be_appended[AUTOQ::Automata<Symbol>::SymbolTag(aut.qubitNum + t.first.symbol().qubit(), new_color_pair)];
                        for (const auto &out_ins : t.second) {
                            auto &container = ref[the_top_state_of_that_leaf_transition];
                            for (auto in : out_ins.second) {
                                for (unsigned i=0; i<in.size(); i++) {
                                    in[i] += aut.stateNum;
                                }
                                container.insert(in);
                            }
                        }
                    } else { // other transitions
                        auto &ref = transitions_to_be_appended[AUTOQ::Automata<Symbol>::SymbolTag(aut.qubitNum + t.first.symbol().qubit(), t.first.tag())];
                        for (const auto &out_ins : t.second) {
                            auto out = out_ins.first;
                            out += aut.stateNum;
                            auto &container = ref[out];
                            for (auto in : out_ins.second) {
                                for (unsigned i=0; i<in.size(); i++) {
                                    in[i] += aut.stateNum;
                                }
                                container.insert(in);
                            }
                        }
                    }
                }
            }
            aut.transitions.erase(it++); // (4)
            aut.stateNum += aut2.stateNum;
        } else {
            ++it;
        }
    }
    for (const auto &t : transitions_to_be_appended) {
        aut.transitions[t.first] = t.second;
    }
    aut.qubitNum += aut2.qubitNum;
    aut.reduce();
    for (const auto &var : aut2.vars)
        aut.vars.insert(var);
    return aut;
}

template <typename Symbol>
AUTOQ::Automata<Symbol> AUTOQ::Automata<Symbol>::operator||(const Automata<Symbol> &o) const {
    if (this->qubitNum == 0) return o;
    if (o.qubitNum == 0) return *this;

    Automata<Symbol> result;
    result = *this;
    result.name = "operator||";
    if (result.qubitNum != o.qubitNum) {
        THROW_AUTOQ_ERROR("Two automata of different numbers of qubits cannot be unioned together.");
    }
    result.stateNum += o.stateNum;
    // TODO: How to check if the two input automata have different k's?

    for (const auto &t : o.transitions) {
        auto &container = result.transitions[t.first];
        for (const auto &out_ins : t.second) {
            auto out = out_ins.first;
            out += this->stateNum;
            auto &sub_container = container[out];
            for (auto in : out_ins.second) {
                for (unsigned i=0; i<in.size(); i++) {
                    in[i] += this->stateNum;
                }
                sub_container.insert(in);
            }
        }
    }
    for (const auto &s : o.finalStates) {
        result.finalStates.push_back(s + this->stateNum);
    }
    result.reduce();
    for (const auto &var : o.vars)
        result.vars.insert(var);
    result.constraints += o.constraints;
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
    return result;
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::SwapDown(int q) {
    assert(!hasLoop);
    TopDownTransitions old_transitions_at_q;
    std::map<State, std::set<std::pair<Tag, StateVector>>> old_transitions_at_q_plus_1;

    // Step 1. Delete all old transitions at level (q) and (q+1).
    Symbol sym_at_q, sym_at_q_plus_1;
    auto transitions_copy = transitions;
    for (const auto &tr : transitions_copy) {
        if (tr.first.symbol().is_internal()) {
            if (tr.first.symbol().qubit() == q) {
                transitions.erase(tr.first);
                old_transitions_at_q.insert(tr);
                sym_at_q = tr.first.symbol(); // save the symbol at level (q)
            }
            if (tr.first.symbol().qubit() == q+1) {
                transitions.erase(tr.first);
                for (const auto &out_ins : tr.second) {
                    for (const auto &in : out_ins.second) {
                        old_transitions_at_q_plus_1[out_ins.first].insert({tr.first.tag(), in});
                    }
                }
                sym_at_q_plus_1 = tr.first.symbol(); // save the symbol at level (q+1)
            }
            if (tr.first.symbol().qubit() >= q+2) {
                break;
            }
        } else {
            break;
        }
    }

    // Step 2. Rewrite the new transitions at level (q) and (q+1).
    std::set<State> states_has_appeared;
    for (const auto &tr : old_transitions_at_q) {
        for (const auto &out_ins : tr.second) {
            for (const auto &in : out_ins.second) {
                assert(in.size() == 2);
                auto leftChild = in.at(0);
                auto rightChild = in.at(1);
                if (states_has_appeared.contains(in.at(0))) leftChild = stateNum++;
                if (states_has_appeared.contains(in.at(1))) rightChild = stateNum++;
                transitions[SymbolTag(sym_at_q, tr.first.tag())][out_ins.first].insert({leftChild, rightChild}); // rewrite at level (q)
                states_has_appeared.insert(in.at(0));
                states_has_appeared.insert(in.at(1));
                for (const auto &c1in1 : old_transitions_at_q_plus_1.at(in.at(0))) {
                    const auto &c1 = c1in1.first;
                    const auto &in1 = c1in1.second;
                    for (const auto &c2in2 : old_transitions_at_q_plus_1.at(in.at(1))) {
                        const auto &c2 = c2in2.first;
                        const auto &in2 = c2in2.second;
                        const auto c = c1 & c2;
                        if (c) {
                            transitions[SymbolTag(sym_at_q_plus_1, c)][leftChild].insert({in1.at(0), in2.at(0)}); // rewrite at level (q+1)
                            transitions[SymbolTag(sym_at_q_plus_1, c)][rightChild].insert({in1.at(1), in2.at(1)}); // rewrite at level (q+1)
                        }
                    }
                }
            }
        }
    }
    auto start = std::chrono::steady_clock::now();
    bottom_up_reduce(q+1);
    auto duration = std::chrono::steady_clock::now() - start;
    total_reduce_time += duration;
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
}
template <typename Symbol>
void AUTOQ::Automata<Symbol>::SwapUp(int q) {
    SwapDown(q-1);
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Predicate>;