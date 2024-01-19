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

using namespace std;
using AUTOQ::Util::ShellCmd;
using AUTOQ::Util::ReadFile;

int type, n;
std::string toString(std::chrono::steady_clock::duration tp);

int main(int argc, char **argv) {
try {
    std::string constraint, constraintQ;
    AUTOQ::TreeAutomata aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::split_automaton_and_constraint(argv[1], constraint);
    aut.remove_useless();
    aut.reduce();
    auto start = chrono::steady_clock::now();
    bool verify = aut.execute(argv[2], constraint);
    AUTOQ::TreeAutomata Q = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::split_automaton_and_constraint(argv[3], constraintQ);
    Q.remove_useless();
    Q.reduce();
    verify &= is_scaled_spec_satisfied(aut, Q);
    std::cout << aut.qubitNum << " & " << AUTOQ::TreeAutomata::gateCount
        << " & " << (verify ? "OK" : "Bug") << " & " << toString(chrono::steady_clock::now() - start) << " & " << getPeakRSS() / 1024 / 1024 << "MB\n";
    return 0;
} catch (std::exception &e) {
    std::cout << e.what() << std::endl;
    return 0;
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
