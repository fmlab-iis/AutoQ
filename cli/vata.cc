#include <fstream>
#include <iostream>
#include <vata/parsing/timbuk_parser.hh>
#include <vata/serialization/timbuk_serializer.hh>
#include <vata/util/aut_description.hh>
#include <vata/util/util.hh>
#include <sys/wait.h>
#include <unistd.h>

#include <chrono>
#include <iomanip>
#include <regex>

using namespace std;
using VATA::Util::TreeAutomata;
using VATA::Util::ShellCmd;
using VATA::Util::ReadFile;

int type, n;

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

std::string toString(std::chrono::steady_clock::duration tp)
{
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
    if (d.count() > 0 || h.count() > 0)
        ss << "TOO_LONG & ";
    else if (m.count() == 0 && s.count() < 10) {
        ss << s.count() << '.' << ms.count() / 100 << "s";
    } else {
        if (m.count() > 0) ss << m.count() << 'm';
        ss << s.count() << 's';// << " & ";
    }
    ss.fill(fill);
    return ss.str();
}

// std::string toString(int tp) // expect unit: ms
// {
//     using namespace std;
//     using namespace std::chrono;
//     milliseconds ns(tp);
//     typedef duration<int, ratio<86400>> days;
//     std::stringstream ss;
//     char fill = ss.fill();
//     ss.fill('0');
//     auto d = duration_cast<days>(ns);
//     ns -= d;
//     auto h = duration_cast<hours>(ns);
//     ns -= h;
//     auto m = duration_cast<minutes>(ns);
//     ns -= m;
//     auto s = duration_cast<seconds>(ns);
//     ns -= s;
//     auto ms = duration_cast<milliseconds>(ns);
//     // auto s = duration<float, std::ratio<1, 1>>(ns);
//     if (d.count() > 0 || h.count() > 0)
//         ss << "TOO_LONG & ";
//     else if (m.count() == 0 && s.count() < 10) {
//         ss << s.count() << '.' << ms.count() / 100 << "s";
//     } else {
//         if (m.count() > 0) ss << m.count() << 'm';
//         ss << s.count() << 's';// << " & ";
//     }
//     ss.fill(fill);
//     return ss.str();
// }

int main(int argc, char **argv) {
    for (int n=2; n<=22; n++) {
        /* Algorithm 9 - Grover's Search with only one oracle */
        VATA::Util::TreeAutomata aut = VATA::Util::TreeAutomata::zero((n+1) + (n>=3) * (n-1));
        std::ofstream pre("/home/alan23273850/libvata2/benchmarks/Grover/" + std::to_string(n) + "/pre.aut");
        aut.fraction_simplication();
        pre << VATA::Serialization::TimbukSerializer::Serialize(aut);
        pre.close();

        // std::ofstream qasm("/home/alan23273850/libvata2/benchmarks/Grover/" + std::to_string(n) + "/circuit.qasm");
        // qasm << "OPENQASM 2.0;\n";
        // qasm << "include \"qelib1.inc\";\n";
        // qasm << "qreg qubits[" + std::to_string(aut.qubitNum) + "];\n";
        // qasm.close();
        aut.X(n+1); // for preparing the initial state
        // system(("echo '' >> /home/alan23273850/libvata2/benchmarks/Grover/" + std::to_string(n) + "/circuit.qasm").c_str());

        auto start = chrono::steady_clock::now();
        int stateBefore = aut.stateNum, transitionBefore = aut.transition_size();
        unsigned ans = 0;
        for (int i=0; i<n; i++) {
            ans <<= 1;
            ans |= (i&1);
        }
        for (int i=1; i<=n+1; i++) aut.H(i);
        for (int iter=1; iter <= M_PI / (4 * asin(1 / pow(2, n/2.0))); iter++) {
            for (int i=1; i<=n; i++) {
                if ((ans & (1 << (i-1))) == 0)
                    aut.X(n+1-i);
            }
            /* multi-controlled NOT gate */
            if (n >= 3) {
                aut.Toffoli(1, 2, n+2);
                for (int i=3; i<=n; i++)
                    aut.Toffoli(i, n+i-1, n+i);
                aut.CNOT(2*n, n+1);
                for (int i=n; i>=3; i--)
                    aut.Toffoli(i, n+i-1, n+i);
                aut.Toffoli(1, 2, n+2);
            } else {
                assert(n == 2);
                aut.Toffoli(1, 2, 3);
            }
            for (int i=1; i<=n; i++) {
                if ((ans & (1 << (i-1))) == 0)
                    aut.X(n+1-i);
            }
            for (int i=1; i<=n; i++) aut.H(i);
            for (int i=1; i<=n; i++) aut.X(i);
            /* multi-controlled Z gate */
            if (n >= 3) {
                aut.Toffoli(1, 2, n+2);
                for (int i=3; i<n; i++) // Note that < does not include n!
                    aut.Toffoli(i, n+i-1, n+i);
                aut.CZ(2*n-1, n);
                for (int i=n-1; i>=3; i--)
                    aut.Toffoli(i, n+i-1, n+i);
                aut.Toffoli(1, 2, n+2);
            // } else if (n == 3) {
            //     aut.H(2*n);
            //     aut.Toffoli(4, 5, 6);
            //     aut.H(2*n);
            } else {
                assert(n == 2);
                aut.CZ(1, 2);
            }
            for (int i=1; i<=n; i++) aut.X(i);
            for (int i=1; i<=n; i++) aut.H(i);
        }

        std::ofstream fileLhs("/home/alan23273850/libvata2/benchmarks/Grover/" + std::to_string(n) + "/post.aut");
        aut.fraction_simplication();
        fileLhs << VATA::Serialization::TimbukSerializer::Serialize(aut);
        fileLhs.close();
        if (!VATA::Util::TreeAutomata::check_equal("/home/alan23273850/libvata2/benchmarks/Grover/" + std::to_string(n) + "/post.aut", "/home/alan23273850/libvata2/benchmarks/Grover/" + std::to_string(n) + "/post.aut")) {
            throw std::exception();
        }

        auto end = chrono::steady_clock::now();
        auto duration = end - start;
        std::cout << n << " & " << VATA::Util::Convert::ToString(aut.qubitNum) << " & " << VATA::Util::TreeAutomata::gateCount << " & " << stateBefore << " & " << aut.stateNum << " & " << transitionBefore << " & " << aut.transition_size()
                        << " & " << VATA::Util::TreeAutomata::binop_time * 100 / duration
                        << "\\% & " << VATA::Util::TreeAutomata::branch_rest_time * 100 / duration
                        << "\\% & " << VATA::Util::TreeAutomata::value_rest_time * 100 / duration
                        << "\\% & " << toString(duration) << "\\\\\\hline\n";
        // std::cout << /*n << ": " <<*/ chrono::duration_cast<chrono::milliseconds>(end - start).count() << " & ";
    }
    return 0;
}
