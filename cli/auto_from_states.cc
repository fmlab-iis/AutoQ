#include <autoq/util/aut_description.hh>

using namespace std;
using AUTOQ::Util::TreeAutomata;

TreeAutomata from_string_to_automaton(std::string tree) {
    TreeAutomata aut;
    std::istringstream iss(tree);
    std::vector<TreeAutomata::InitialSymbol> states_probs;
    TreeAutomata::InitialSymbol default_prob;
    for (std::string state_prob; iss >> state_prob;) {
        std::istringstream iss2(state_prob);
        std::string state;
        std::getline(iss2, state, ':');
        if (states_probs.empty()) {
            aut.qubitNum = state.length();
            states_probs.resize(pow(2, state.length()));
        }
        std::string t;
        if (state == "*") {
            while (std::getline(iss2, t, ',')) {
                default_prob.push_back(std::atoi(t.c_str()));
            }
        } else {
            int s = std::stoi(state, nullptr, 2);
            while (std::getline(iss2, t, ',')) {
                states_probs[s].push_back(std::atoi(t.c_str()));
            }
        }
    }
    int pow_of_two = 1;
    TreeAutomata::State state_counter = 0;
    for (int level=1; level<=aut.qubitNum; level++) {
        for (int i=0; i<pow_of_two; i++) {
            aut.transitions[{level}][{state_counter*2+1, state_counter*2+2}] = {state_counter};
            state_counter++;
        }
        pow_of_two *= 2;
    }
    for (TreeAutomata::State i=state_counter; i<=state_counter*2; i++) {
        if (states_probs[i-state_counter].empty())
            aut.transitions[default_prob][{}].insert(i);
        else
            aut.transitions[states_probs[i-state_counter]][{}].insert(i);
    }
    aut.finalStates.push_back(0);
    aut.stateNum = state_counter*2 + 1;
    aut.reduce();

    return aut;
}

int main(int argc, char **argv) {
    TreeAutomata aut_final;
    std::string line;
    while (std::cout << "> " && std::getline(std::cin, line)) {
        std::istringstream iss_tensor(line);
        std::string tree;
        std::getline(iss_tensor, tree, '#');

        auto aut = from_string_to_automaton(tree); // the first automata to be tensor producted

        // to tensor product with the rest of the automata
        while (std::getline(iss_tensor, tree, '#')) {
            auto aut2 = from_string_to_automaton(tree);

            // let aut2 be tensor producted with aut here
            TreeAutomata::TransitionMap aut_leaves;
            for (const auto &t : aut.transitions) {
                if (t.first.is_leaf()) {
                    aut_leaves[t.first] = t.second;
                }
            }
            for (const auto &t : aut_leaves) {
                aut.transitions.erase(t.first);
            }

            // append aut2 to each leaf transition of aut
            for (const auto &t : aut_leaves) {
                for (const auto &t2 : aut2.transitions) {
                    if (t2.first.is_internal()) { // if the to-be-appended transition is internal, then
                        auto Q = aut.qubitNum + t2.first.initial_symbol().at(0); // we need to shift the qubit number
                        for (const auto &kv : t2.second) { // for each pair of vec_in -> set_out
                            auto k = kv.first;
                            for (int i=0; i<k.size(); i++)
                                k.at(i) += aut.stateNum;
                            // above shift the state number of vec_in first,
                            for (const auto &s : kv.second) {
                                if (s == 0) { // if to be connected to leaf states of aut, then
                                    for (const auto &s2 : t.second.at({})) // simply apply these states
                                        aut.transitions[{Q}][k].insert(s2);
                                }
                                else // and then shift the state number of set_out
                                    aut.transitions[{Q}][k].insert(s + aut.stateNum);
                            }
                        }
                    } else {
                        for (const auto &kv : t2.second) {
                            auto k = kv.first;
                            for (int i=0; i<k.size(); i++)
                                k.at(i) += aut.stateNum;
                            for (const auto &s : kv.second) {
                                aut.transitions[t.first.initial_symbol() * t2.first.initial_symbol()][k].insert(s + aut.stateNum);
                            }
                        }
                    }
                }
                aut.stateNum += aut2.stateNum;
            }
            aut.qubitNum += aut2.qubitNum;
            aut.reduce();
        }
        aut_final = aut_final.Union(aut);
        aut_final.reduce();
    }
    aut_final.fraction_simplification();
    aut_final.reduce();
    std::cout << std::endl;
    aut_final.print();
    return 0;
}