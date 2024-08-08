#include <fstream>
#include <iostream>
#include <autoq/parsing/timbuk_parser.hh>
#include <autoq/serialization/timbuk_serializer.hh>
#include <autoq/aut_description.hh>
#include <autoq/inclusion.hh>
#include <autoq/util/util.hh>
#include <autoq/complex/complex.hh>
#include <iomanip>

using namespace std;
using AUTOQ::TreeAutomata;
using AUTOQ::Util::ShellCmd;
using AUTOQ::Util::ReadFile;

int main(int argc, char **argv) {
    enum { P, Q1, Q0 };
    AUTOQ::TreeAutomata aut;
    aut.hasLoop = true;
    aut.finalStates.push_back(P);
    aut.stateNum = 3;
    aut.qubitNum = 0;
    aut.transitions[{1, 0b01}][P].insert({Q1, Q0});
    aut.transitions[{1, 0b01}][Q1].insert({Q1, Q0});
    aut.transitions[{1, 0b01}][Q0].insert({Q0, Q0});
    aut.transitions[{AUTOQ::Complex::Complex::Zero(), 0b10}][Q0].insert({{}});
    aut.transitions[{AUTOQ::Complex::Complex::One(), 0b10}][Q1].insert({{}});
    // aut.print_aut("Pre-condition:\n");

    aut.initialize_stats();
    aut.unfold_top();
    aut.H(1);
    aut.fold();
    aut.CX();
    AUTOQ::TreeAutomata::stop_execute = std::chrono::steady_clock::now();
    // aut.print_aut("Result:\n");

    enum { p, qL, qR, q0 };
    AUTOQ::TreeAutomata ans;
    ans.hasLoop = true;
    ans.finalStates.push_back(p);
    ans.stateNum = 4;
    ans.qubitNum = 0;
    ans.transitions[{1, 0b01}][p].insert({qL, qR});
    ans.transitions[{1, 0b01}][qL].insert({qL, q0});
    ans.transitions[{AUTOQ::Complex::Complex::One().divide_by_the_square_root_of_two(), 0b10}][qL].insert({{}});
    ans.transitions[{1, 0b01}][qR].insert({q0, qR});
    ans.transitions[{AUTOQ::Complex::Complex::One().divide_by_the_square_root_of_two(), 0b10}][qR].insert({{}});
    ans.transitions[{1, 0b01}][q0].insert({q0, q0});
    ans.transitions[{AUTOQ::Complex::Complex::Zero(), 0b10}][q0].insert({{}});
    // ans.print_aut("Post-condition:\n");

    aut == ans;
    aut.print_stats();
    return 0;
}
