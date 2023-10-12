#include <fstream>
#include <iostream>
#include <autoq/parsing/timbuk_parser.hh>
#include <autoq/serialization/timbuk_serializer.hh>
#include <autoq/aut_description.hh>
#include <autoq/inclusion.hh>
#include <autoq/util/util.hh>
#include <util_sim.h>
#include <sys/wait.h>
#include <unistd.h>

#include <chrono>
#include <iomanip>
#include <regex>

#include "autoq/complex/complex.hh"

using namespace std;
using AUTOQ::TreeAutomata;
using AUTOQ::Util::ShellCmd;
using AUTOQ::Util::ReadFile;
using AUTOQ::Symbol::Concrete;
using AUTOQ::Complex::Complex;

int type, n;

int rand_gen();
void rand_gen(int &a, int &b);
void rand_gen(int &a, int &b, int &c);
std::string toString(std::chrono::steady_clock::duration tp);

AUTOQ::TreeAutomata colored_aut() {
    TreeAutomata aut;
    aut.qubitNum = 2;
    aut.transitions[{TreeAutomata::Symbol(1), TreeAutomata::Tag(1)}][{1,2}].insert(0);
    aut.transitions[{TreeAutomata::Symbol(1), TreeAutomata::Tag(2)}][{3,4}].insert(0);
    aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(1)}][{5,5}].insert(1);
    aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(1)}][{5,5}].insert(4);
    aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(1)}][{5,6}].insert(2);
    aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(1)}][{5,6}].insert(3);
    aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(2)}][{5,5}].insert(1);
    aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(2)}][{5,5}].insert(4);
    aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(2)}][{6,5}].insert(2);
    aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(2)}][{6,5}].insert(3);
    // aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(3)}][{7,8}].insert(1);
    // aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(3)}][{7,8}].insert(4);
    // aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(3)}][{8,7}].insert(1);
    // aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(3)}][{8,7}].insert(4);
    // aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(3)}][{8,8}].insert(2);
    // aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(3)}][{8,8}].insert(3);
    aut.transitions[Concrete(Complex::One().divide_by_the_square_root_of_two(2) * (-1))][{}].insert(7);
    aut.transitions[Concrete(Complex::Zero())][{}].insert(5);
    aut.transitions[Concrete(Complex::One())][{}].insert(6);
    aut.transitions[Concrete(Complex::One().divide_by_the_square_root_of_two(2))][{}].insert(8);
    aut.finalStates.push_back(0);
    aut.stateNum = 9;
    return aut;
}

AUTOQ::TreeAutomata uncolored_aut() {
    TreeAutomata aut;
    aut.qubitNum = 2;
    aut.transitions[{TreeAutomata::Symbol(1), TreeAutomata::Tag(0)}][{1,2}].insert(0);
    aut.transitions[{TreeAutomata::Symbol(1), TreeAutomata::Tag(0)}][{3,4}].insert(0);
    aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(0)}][{5,5}].insert(1);
    aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(0)}][{5,5}].insert(4);
    aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(0)}][{5,6}].insert(2);
    aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(0)}][{5,6}].insert(3);
    aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(0)}][{5,5}].insert(1);
    aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(0)}][{5,5}].insert(4);
    aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(0)}][{6,5}].insert(2);
    aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(0)}][{6,5}].insert(3);
    // aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(0)}][{7,8}].insert(1);
    // aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(0)}][{7,8}].insert(4);
    // aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(0)}][{8,7}].insert(1);
    // aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(0)}][{8,7}].insert(4);
    // aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(0)}][{8,8}].insert(2);
    // aut.transitions[{TreeAutomata::Symbol(2), TreeAutomata::Tag(0)}][{8,8}].insert(3);
    aut.transitions[Concrete(Complex::One().divide_by_the_square_root_of_two(2) * (-1))][{}].insert(7);
    aut.transitions[Concrete(Complex::Zero())][{}].insert(5);
    aut.transitions[Concrete(Complex::One())][{}].insert(6);
    aut.transitions[Concrete(Complex::One().divide_by_the_square_root_of_two(2))][{}].insert(8);
    aut.finalStates.push_back(0);
    aut.stateNum = 9;
    return aut;
}

int main(int argc, char **argv) {
    auto aut1 = uncolored_aut();
    auto aut2 = aut1;
    aut1.print("Before\n");
    aut1.reduce();
    aut1.print("\nAfter light reduce\n");
    aut2.sim_reduce();
    aut2.print("\nAfter sim_reduce\n");
}

int rand_gen() {
    if (type == 3) return 1;
    else if (type == 5) return n;
    else return rand() % n + 1;
}
void rand_gen(int &a, int &b) {
    if (type == 3) { // TOP
        a = 1;
        b = 2;
    } else if (type == 5) { // BOTTOM
        a = n-1;
        b = n;
    } else {
        a = rand() % n + 1;
        do {
            b = rand() % n + 1;
        } while (b == a);
    }
}
void rand_gen(int &a, int &b, int &c) {
    if (type == 3) { // TOP
        a = 1;
        b = 2;
        c = 3;
    } else if (type == 5) { // BOTTOM
        a = n-2;
        b = n-1;
        c = n;
    } else {
        a = rand() % n + 1;
        do {
            b = rand() % n + 1;
        } while (b == a);
        do {
            c = rand() % n + 1;
        } while (c == a || c == b);
    }
}

std::string toString(std::chrono::steady_clock::duration tp) {
    using namespace std;
    using namespace std::chrono;
    nanoseconds ns = duration_cast<nanoseconds>(tp);
    typedef duration<int, ratio<86400>> days;
    std::stringstream ss;
    char fill = ss.fill();
    ss.fill('0');
    auto d = duration_cast<days>(ns);
    ns -= d;
    auto h = duration_cast<hours>(ns);
    ns -= h;
    auto m = duration_cast<minutes>(ns);
    ns -= m;
    auto s = duration_cast<seconds>(ns);
    ns -= s;
    auto ms = duration_cast<milliseconds>(ns);
    // auto s = duration<float, std::ratio<1, 1>>(ns);
    if (d.count() > 0)
        ss << d.count() << 'd' << h.count() << 'h' << m.count() << 'm' << s.count() << 's';
    else if (h.count() > 0)
        ss << h.count() << 'h' << m.count() << 'm' << s.count() << 's';
    else if (m.count() == 0 && s.count() < 10) {
        ss << s.count() << '.' << ms.count() / 100 << "s";
    } else {
        if (m.count() > 0) ss << m.count() << 'm';
        ss << s.count() << 's';// << " & ";
    }
    ss.fill(fill);
    return ss.str();
}
