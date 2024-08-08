#include <autoq/aut_description.hh>
#include <autoq/symbol/concrete.hh>
#include <autoq/symbol/symbolic.hh>

template <typename Symbol>
void AUTOQ::Automata<Symbol>::unfold_top() {
    TopDownTransitions transitions_insert;
    std::map<SymbolTag, std::vector<StateVector>> transitions_delete;
    for (const auto &fc_ois : transitions) {
        const auto &fc = fc_ois.first;
        const auto &ois = fc_ois.second;
        auto &transitions_insert_fc = transitions_insert[fc];
        auto &transitions_insert_fc2 = fc.symbol().is_internal() ? transitions_insert[{fc.symbol().qubit()+1, fc.second}] : transitions_insert_fc;
        auto &transitions_delete_fc = transitions_delete[fc];
        for (const auto &oi : ois) {
            const auto &top = oi.first;
            const auto &ins = oi.second;
            if (fc.symbol().is_leaf()) {
                transitions_insert_fc[top + stateNum].insert({{}});
            } else if (fc.symbol().qubit() == qubitNum+1) {
                auto &transitions_insert_fc_top = transitions_insert_fc[top];
                auto &transitions_insert_fc2_top_stateNum = transitions_insert_fc2[top + stateNum];
                for (auto in : ins) {
                    transitions_delete_fc.push_back(in);
                    for_each(in.begin(), in.end(), [this](auto &n) { n += stateNum; });
                    transitions_insert_fc2_top_stateNum.insert(in);
                    transitions_insert_fc_top.insert(in);
                }
            }
        }
    }
    for (const auto &fc_ins : transitions_delete) {
        const auto &fc = fc_ins.first;
        const auto &ins = fc_ins.second;
        for (auto &ois : transitions[fc]) {
            auto &oissecond = ois.second;
            for (const auto &in : ins) {
                oissecond.erase(in);
            }
        }
    }
    for (const auto &fc_ois : transitions_insert) {
        const auto &fc = fc_ois.first;
        const auto &ois = fc_ois.second;
        auto &transitions_fc = transitions[fc];
        for (const auto &oi : ois) {
            const auto &out = oi.first;
            const auto &ins = oi.second;
            transitions_fc[out].insert(ins.begin(), ins.end());
        }
    }
    stateNum *= 2;
    qubitNum++;
    remove_useless();
    reduce();
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::unfold_bottom() {
    TopDownTransitions transitions_result;
    for (const auto &fc_ois : transitions) {
        const auto &fc = fc_ois.first;
        const auto &ois = fc_ois.second;
        auto &transitions_result_fc = transitions_result[fc];
        auto &transitions_result_fc_shift = fc.first.is_internal() ? transitions_result[{fc.first.qubit(), fc.second << 2}] : transitions_result_fc; // TODO: temporary solution
        auto &transitions_result_shift = fc.first.is_internal() ? transitions_result[{fc.first.qubit() + 1, fc.second}] : transitions_result_fc;
        for (const auto &oi : ois) {
            const auto &top = oi.first;
            const auto &ins = oi.second;
            if (fc.first.is_leaf()) {
                transitions_result_fc[top].insert(ins.begin(), ins.end());
            } else { // internal
                if (fc.first.qubit() == 1) {
                    auto &ref = transitions_result_fc_shift[top + stateNum];
                    for (auto in : ins) {
                        for_each(in.begin(), in.end(), [this](auto &n) { n += stateNum; });
                        ref.insert(in);
                    }
                    transitions_result_shift[top + stateNum].insert(ins.begin(), ins.end());
                } else {
                    transitions_result_shift[top].insert(ins.begin(), ins.end());
                }
            }
        }
    }
    transitions = transitions_result;
    for (unsigned i=0; i<finalStates.size(); i++)
        finalStates.at(i) += stateNum;
    stateNum *= 2;
    qubitNum++;
    remove_useless();
    reduce();
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::fold() {
    TopDownTransitions transitions_result;
    for (const auto &fc_ois : transitions) {
        const auto &fc = fc_ois.first;
        const auto &ois = fc_ois.second;
        auto &transitions_result_fc = transitions_result[fc];
        auto &transitions_result_fc2 = transitions_result[{1, fc.second}];
        for (const auto &oi : ois) {
            const auto &top = oi.first;
            const auto &ins = oi.second;
            if (fc.first.is_internal())
                transitions_result_fc2[top].insert(ins.begin(), ins.end());
            else
                transitions_result_fc[top].insert(ins.begin(), ins.end());
        }
    }
    transitions = transitions_result;
    qubitNum = 0;
    remove_useless();
    reduce();
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;