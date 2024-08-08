#include "autoq/aut_description.hh"
#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/symbol/predicate.hh"
#include "autoq/symbol/index.hh"
#include "autoq/serialization/timbuk_serializer.hh"
#include <boost/dynamic_bitset.hpp> // used in print_language

template <typename Symbol>
void AUTOQ::Automata<Symbol>::initialize_stats() {
    stateBefore = stateNum;
    transitionBefore = count_transitions();
    start_execute = std::chrono::steady_clock::now();
}

template <typename Symbol>
int AUTOQ::Automata<Symbol>::count_leaves() const {
    int answer = 0;
    for (const auto &t : transitions) {
        if (t.first.is_leaf())
            answer++;
    }
    return answer;
}

template <typename Symbol>
int AUTOQ::Automata<Symbol>::count_states() const {
    int maxState = 0;
    for (const auto &t : transitions) {
        for (const auto &out_ins : t.second) {
            if (maxState < out_ins.first)
                maxState = out_ins.first;
            for (const auto &in : out_ins.second) {
                for (const auto &s : in) {
                    if (maxState < s)
                        maxState = s;
                }
            }
        }
    }
    return maxState + 1;
}

template <typename Symbol>
int AUTOQ::Automata<Symbol>::count_transitions() const {
    int count = 0;
    for (const auto &t : transitions)
        for (const auto &out_ins : t.second) {
            count += out_ins.second.size();
        }
    return count;
}

template <typename Symbol> // qubit: int, all colors: AUTOQ::Automata<Symbol>::Tag
// returns a set of trees and all colors used in each layer for each tree
std::vector<std::pair<std::map<int, typename AUTOQ::Automata<Symbol>::Tag>, std::vector<std::string>>> get_all_languages_under_the_state_at_this_level(
    const AUTOQ::Automata<Symbol> &aut,
    const std::map<typename AUTOQ::Automata<Symbol>::State, std::vector<typename AUTOQ::Automata<Symbol>::SymbolTag>> &leafSymbolTagsMap,
    const std::map<int, std::map<typename AUTOQ::Automata<Symbol>::State, std::vector<typename AUTOQ::Automata<Symbol>::Tag>>> &dqCOLORs,
    int qubit, typename AUTOQ::Automata<Symbol>::State top) {
    std::vector<std::pair<std::map<int, typename AUTOQ::Automata<Symbol>::Tag>, std::vector<std::string>>> answers;
    if (qubit == static_cast<int>(aut.qubitNum + 1)) {
        for (const auto &symbol_tag : leafSymbolTagsMap.at(top)) {
            std::stringstream ss;
            ss << symbol_tag.symbol();
            answers.push_back({{{qubit, symbol_tag.tag()}}, {ss.str()}});
        }
        // std::cout << AUTOQ::Util::Convert::ToString(answers) << "\n";
        return answers;
    }
    for (const auto &tr : aut.transitions) {
        if (tr.first.symbol().is_internal() && tr.first.symbol().qubit()==qubit) {
            for (const auto &out_ins : tr.second) {
                if (out_ins.first == top) { // the topmost transition's top state must contain "q"
                    for (const auto &in : out_ins.second) {
                        // List all left subtrees below layer "qubit" rooted at the left child of this transition
                        auto all_left_trees = get_all_languages_under_the_state_at_this_level(aut, leafSymbolTagsMap, dqCOLORs, qubit + 1, in.at(0));
                        // List all right subtrees below layer "qubit" rooted at the right child of this transition
                        auto all_right_trees = get_all_languages_under_the_state_at_this_level(aut, leafSymbolTagsMap, dqCOLORs, qubit + 1, in.at(1));
                        for (const auto &L : all_left_trees) { // L: one left tree data structure
                            const auto &colorsL = L.first; // all used colors in each layer of L
                            for (const auto &R : all_right_trees) { // R: one right tree data structure
                                auto subtreeL = L.second; // this left subtree
                                const auto &colorsR = R.first; // all used colors in each layer of R
                                const auto &subtreeR = R.second; // this right subtree
                                std::map<int, typename AUTOQ::Automata<Symbol>::Tag> colorsLtR; // construct all newly used colors in each layer of L+R so far
                                for (const auto &kv : colorsL) { // in fact d > qubit
                                    const auto d = kv.first; // in fact will loop through each layer below this layer
                                    colorsLtR[d] = kv.second & colorsR.at(d); // of course union the left color"s" and the right color"s"
                                    if (colorsLtR[d] == 0)
                                        goto FAIL;
                                    // for (const auto &qCOL : dqCOLORs.at(d)) { // inspect all top states q used in this layer
                                    //     // and check if there are at least two transitions under this q included in colorsLtR[d]
                                    //     // if yes, then fail (this LR cannot be used in the future).
                                    //     int count = 0;
                                    //     for (const auto &color : qCOL.second) { // loop through all transitions
                                    //         count += (colorsLtR[d] == (colorsLtR[d] | color)); // color is included in colorsLtR[d]
                                    //         if (count >= 2) goto FAIL;
                                    //     }
                                    // }
                                }
                                // so far has merged all used colors in L+R so far
                                colorsLtR[qubit] = tr.first.tag(); // now we want to add the color of the used transition in this layer
                                if (colorsLtR[qubit] == 0)
                                    goto FAIL;
                                // for (const auto &qCOL : dqCOLORs.at(qubit)) { // inspect all top states q used in this layer
                                //     // and check if there are at least two transitions under this q included in colorsLtR[qubit]
                                //     // if yes, then fail (this LtR cannot be used in the future).
                                //     int count = 0;
                                //     for (const auto &color : qCOL.second) { // loop through all transitions
                                //         count += (colorsLtR[qubit] == (colorsLtR[qubit] | color)); // color is included in colorsLtR[qubit]
                                //         if (count >= 2) goto FAIL;
                                //     }
                                // }
                                subtreeL.insert(subtreeL.end(), subtreeR.begin(), subtreeR.end());
                                answers.push_back({colorsLtR, subtreeL}); // now subtreeL actually becomes subtreeLtR
                                FAIL: {}
                            }
                        }
                    }
                }
            }
        }
    }
    // std::cout << AUTOQ::Util::Convert::ToString(answers) << "\n";
    return answers;
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::print_language(const std::string &str) const {
    std::cout << str;
    std::map<State, std::vector<SymbolTag>> leafSymbolTagsMap;
    std::map<int, std::map<State, std::vector<Tag>>> dqCOLORs;
    for (const auto &t : transitions) {
        for (const auto &out_ins : t.second) { // construct the map from state to leaf symbols
            const auto &q = out_ins.first;
            if (t.first.symbol().is_internal())
                dqCOLORs[static_cast<int>(t.first.symbol().qubit())][q].push_back(t.first.tag());
            else
                dqCOLORs[qubitNum+1][q].push_back(t.first.tag());
        }
        if (t.first.is_leaf()) { // construct the map from state to leaf symbols
            for (const auto &out_ins : t.second) {
                const auto &s = out_ins.first;
                leafSymbolTagsMap[s].push_back(t.first);
            }
        }
    }
    std::set<std::vector<std::string>> result_trees;
    for (const auto &s : finalStates) {
        auto results = get_all_languages_under_the_state_at_this_level(*this, leafSymbolTagsMap, dqCOLORs, 1, s); // many accepted trees
        for (const auto& pair : results) {
            result_trees.insert(pair.second);
        }
    }
    for (const auto &tree : result_trees) { // each result is a tree
        std::map<std::string, int> count;
        for (unsigned i=0; i<tree.size(); i++)
            count[tree[i]]++;
        auto ptr = std::max_element(count.begin(), count.end(), [](const auto &x, const auto &y) {
            return x.second < y.second;
        });
        for (unsigned i=0; i<tree.size(); i++) {
            if (tree[i] != (ptr->first))
                std::cout << boost::dynamic_bitset(qubitNum, i) << ":" << tree[i] << " ";
        }
        std::cout << "*:" << (ptr->first) << std::endl;
    }
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::print_aut(const std::string &prompt) const {
    std::cout << prompt;
    std::cout << AUTOQ::Serialization::TimbukSerializer::Serialize(*this);
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::print_stats(const std::string &str, bool newline) {
    state_renumbering();
    std::cout << str;
    std::cout << AUTOQ::Util::Convert::ToString(qubitNum) << " & " << AUTOQ::TreeAutomata::gateCount
              << " & " << stateBefore << " & " << stateNum
              << " & " << transitionBefore << " & " << count_transitions()
              << " & " << AUTOQ::Util::Convert::toString(stop_execute - start_execute) << " & " << include_status;
    if (newline)
        std::cout << std::endl;
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Predicate>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Index>;