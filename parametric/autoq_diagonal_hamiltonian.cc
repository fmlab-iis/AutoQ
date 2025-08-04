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

int main(int, char**) {
    enum { P, Q1, Q0 };
    AUTOQ::TreeAutomata aut, ans;
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
    ans = aut;

    aut.initialize_stats();
    aut.Phase(boost::rational<boost::multiprecision::cpp_int>(-1, 4)); // aut.print_aut("Phase(-pi/2):\n");
    aut.CX(); // aut.print_aut("CX:\n");
    aut.unfold_bottom(); // aut.print_aut("Unfold:\n");
    aut.Rz(boost::rational<boost::multiprecision::cpp_int>(-1, 2), 2); // aut.print_aut("Phase(pi/2):\n");
    aut.fold(); // aut.print_aut("Fold:\n");
    aut.CX_inv(); // aut.print_aut("CX_inv:\n");
    AUTOQ::TreeAutomata::stop_execute = std::chrono::steady_clock::now();
    // aut.print_aut("Result:\n");

    // ans.print_aut("Post-condition:\n");

    aut == ans;
    aut.print_stats();
    return 0;
}