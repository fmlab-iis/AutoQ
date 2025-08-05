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
    AUTOQ::Complex::nTuple::N = 8;
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

    aut.initialize_stats();
    /////////////////
    aut.unfold_top();
    aut.unfold_top();
    aut.H(2);
    aut.H(1);
    aut.fold();
    aut.unfold_bottom();
    aut.unfold_bottom();
    aut.H(3);
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 8), 2);
    aut.fold();
    aut.CX();
    aut.unfold_bottom();
    aut.Rz(boost::rational<boost::multiprecision::cpp_int>(-1, 4), 2);
    aut.fold();
    aut.CX_inv();
    aut.unfold_top();
    aut.unfold_top();
    aut.H(2);
    aut.H(1);
    aut.fold();
    aut.unfold_bottom();
    aut.unfold_bottom();
    aut.H(3);
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(-1, 8), 2);
    aut.fold();
    ///////////
    aut.unfold_top();
    aut.unfold_top();
    aut.H(2);
    aut.H(1);
    aut.fold();
    aut.unfold_bottom();
    aut.unfold_bottom();
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 8), 3);
    aut.H(2);
    aut.fold();
    aut.CX();
    aut.unfold_bottom();
    aut.Rz(boost::rational<boost::multiprecision::cpp_int>(-1, 4), 2);
    aut.fold();
    aut.CX_inv();
    aut.unfold_top();
    aut.unfold_top();
    aut.H(2);
    aut.H(1);
    aut.fold();
    aut.unfold_bottom();
    aut.unfold_bottom();
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(-1, 8), 3);
    aut.H(2);
    aut.fold();
    ///////////
    aut.unfold_top();
    aut.unfold_top();
    aut.H(1);
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 8), 2);
    aut.fold();
    aut.unfold_bottom();
    aut.unfold_bottom();
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 8), 3);
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 8), 2);
    aut.fold();
    aut.CX();
    aut.unfold_bottom();
    aut.Rz(boost::rational<boost::multiprecision::cpp_int>(-1, 4), 2);
    aut.fold();
    aut.CX_inv();
    aut.unfold_top();
    aut.unfold_top();
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(-1, 8), 2);
    aut.H(1);
    aut.fold();
    aut.unfold_bottom();
    aut.unfold_bottom();
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(-1, 8), 3);
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(-1, 8), 2);
    aut.fold();
    ///////////
    aut.unfold_top();
    aut.unfold_top();
    aut.H(2);
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 8), 1);
    aut.fold();
    aut.unfold_bottom();
    aut.unfold_bottom();
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 8), 3);
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 8), 2);
    aut.fold();
    aut.CX();
    aut.unfold_bottom();
    aut.Rz(boost::rational<boost::multiprecision::cpp_int>(-1, 4), 2);
    aut.fold();
    aut.CX_inv();
    aut.unfold_top();
    aut.unfold_top();
    aut.H(2);
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(-1, 8), 1);
    aut.fold();
    aut.unfold_bottom();
    aut.unfold_bottom();
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(-1, 8), 3);
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(-1, 8), 2);
    aut.fold();
    ///////////
    aut.unfold_top();
    aut.unfold_top();
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 8), 2);
    aut.H(1);
    aut.fold();
    aut.unfold_bottom();
    aut.unfold_bottom();
    aut.H(3);
    aut.H(2);
    aut.fold();
    aut.CX();
    aut.unfold_bottom();
    aut.Rz(boost::rational<boost::multiprecision::cpp_int>(1, 4), 2);
    aut.fold();
    aut.CX_inv();
    aut.unfold_top();
    aut.unfold_top();
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(-1, 8), 2);
    aut.H(1);
    aut.fold();
    aut.unfold_bottom();
    aut.unfold_bottom();
    aut.H(3);
    aut.H(2);
    aut.fold();
    ///////////
    aut.unfold_top();
    aut.unfold_top();
    aut.H(2);
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 8), 1);
    aut.fold();
    aut.unfold_bottom();
    aut.unfold_bottom();
    aut.H(3);
    aut.H(2);
    aut.fold();
    aut.CX();
    aut.unfold_bottom();
    aut.Rz(boost::rational<boost::multiprecision::cpp_int>(1, 4), 2);
    aut.fold();
    aut.CX_inv();
    aut.unfold_top();
    aut.unfold_top();
    aut.H(2);
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(-1, 8), 1);
    aut.fold();
    aut.unfold_bottom();
    aut.unfold_bottom();
    aut.H(3);
    aut.H(2);
    aut.fold();
    ///////////
    aut.unfold_top();
    aut.unfold_top();
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 8), 2);
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 8), 1);
    aut.fold();
    aut.unfold_bottom();
    aut.unfold_bottom();
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 8), 3);
    aut.H(2);
    aut.fold();
    aut.CX();
    aut.unfold_bottom();
    aut.Rz(boost::rational<boost::multiprecision::cpp_int>(1, 4), 2);
    aut.fold();
    aut.CX_inv();
    aut.unfold_top();
    aut.unfold_top();
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(-1, 8), 2);
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(-1, 8), 1);
    aut.fold();
    aut.unfold_bottom();
    aut.unfold_bottom();
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 8), 3);
    aut.H(2);
    aut.fold();
    ///////////
    aut.unfold_top();
    aut.unfold_top();
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 8), 2);
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 8), 1);
    aut.fold();
    aut.unfold_bottom();
    aut.unfold_bottom();
    aut.H(3);
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 8), 2);
    aut.fold();
    aut.CX();
    aut.unfold_bottom();
    aut.Rz(boost::rational<boost::multiprecision::cpp_int>(1, 4), 2);
    aut.fold();
    aut.CX_inv();
    aut.unfold_top();
    aut.unfold_top();
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(-1, 8), 2);
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(-1, 8), 1);
    aut.fold();
    aut.unfold_bottom();
    aut.unfold_bottom();
    aut.H(3);
    aut.Rx(boost::rational<boost::multiprecision::cpp_int>(-1, 8), 2);
    aut.fold();
    ///////////
    aut.stop_execute = std::chrono::steady_clock::now();
    // aut.print_aut("Result:\n");

    ans = aut;
    ans.sim_reduce();
    // ans.print_aut("Post-condition:\n");

    aut <= ans;
    aut.print_stats();
    return 0;
}