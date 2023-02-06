#include <autoq/util/aut_description.hh>

using namespace std;
using AUTOQ::Util::TreeAutomata;

int main(int argc, char **argv) {
    TreeAutomata aut_final;
    std::string line;
    while (std::getline(std::cin, line)) {
        TreeAutomata aut;
        std::istringstream iss(line);
        std::vector<TreeAutomata::InitialSymbol> states_probs;
        TreeAutomata::InitialSymbol default_prob;
        for (std::string state_prob; iss >> state_prob;) {
            // std::cout << state_prob << "\n";
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
        aut_final = aut_final.Union(aut);
        aut_final.reduce();
    }
    aut_final.fraction_simplification();
    aut_final.reduce();
    aut_final.print();
    return 0;
}