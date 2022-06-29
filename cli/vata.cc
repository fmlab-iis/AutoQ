#include <fstream>
#include <iostream>
#include <vata/parsing/timbuk_parser.hh>
#include <vata/serialization/timbuk_serializer.hh>
#include <vata/util/aut_description.hh>
#include <vata/util/util.hh>

#include <chrono>
#include <iomanip>

using namespace std;
using VATA::Parsing::TimbukParser;
using VATA::Serialization::TimbukSerializer;
using VATA::Util::TreeAutomata;
using VATA::Util::ShellCmd;
using VATA::Util::ReadFile;

int type, n;

int rand_gen() {
    if (type == 4) return 1;
    else if (type == 6) return n;
    else return rand() % n + 1;
}

void rand_gen(int &a, int &b) {
    if (type == 4) { // TOP
        a = 1;
        b = 2;
    } else if (type == 6) { // BOTTOM
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
    if (type == 4) { // TOP
        a = 1;
        b = 2;
        c = 3;
    } else if (type == 6) { // BOTTOM
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

int main(int argc, char **argv) {
    type = atoi(argv[1]); // algorithm
    n = atoi(argv[2]); // the gate id / the number of qubits
    if (type == 6) {
        int k = n;
        n = 3;
        while (--k) n <<= 1; // * 2
    }

    int stateBefore = 0, transitionBefore = 0;
    VATA::Util::TreeAutomata aut;
    auto start = chrono::steady_clock::now();
    if (type == 0) {
        aut = VATA::Util::TreeAutomata::classical(10);
        n--;
        switch(n) {
            case 0: aut.X(1); break;
            case 1: aut.Y(1); break;
            case 2: aut.Z(1); break;
            case 3: aut.H(1); break;
            case 4: aut.S(1); break;
            case 5: aut.T(1); break;
            case 6: aut.Rx(1); break;
            case 7: aut.Ry(1); break;
            case 8: aut.CNOT(1, 2); break;
            case 9: aut.CZ(1, 2); break;
            case 10: aut.Toffoli(1, 2, 3); break;
            case 11: aut.Fredkin(1, 2, 3); break;
            default: break;
        }
    } else if (type == 1) { /* Algorithm 1 - Bernstein-Vazirani */
        aut = VATA::Util::TreeAutomata::zero(n+1);
        stateBefore = aut.stateNum, transitionBefore = aut.transition_size();
        for (int i=1; i<=n+1; i++) aut.H(i);
        aut.Z(n+1);
        for (int i=1; i<=n; i++) {
            auto aut2 = aut;
            aut2.CNOT(i, n+1);
            aut = aut.Union(aut2);
        }
        for (int i=1; i<=n; i++) aut.H(i);
    } else if (type == 2) { /* Algorithm 2 - Grover's Search */
        if (!(n >= 2)) throw std::out_of_range("");
        aut = VATA::Util::TreeAutomata::classical_zero_one_zero(n);
        stateBefore = aut.stateNum, transitionBefore = aut.transition_size();
        for (int i=1; i<=n; i++) aut.X(i);
        for (int i=n+1; i<=2*n+1; i++) aut.H(i);
        for (int iter=1; iter <= M_PI / (4 * asin(1 / pow(2, n/2.0))); iter++) {
            for (int i=1; i<=n; i++) aut.CNOT(i, n+i);
            if (n >= 3) {
                aut.Toffoli(n+1, n+2, 2*n+2);
                for (int i=3; i<=n; i++)
                    aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
                aut.CNOT(3*n, 2*n+1);
                for (int i=n; i>=3; i--)
                    aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
                aut.Toffoli(n+1, n+2, 2*n+2);
            } else {
                if (!(n == 2)) throw std::out_of_range("");
                aut.Toffoli(3, 4, 5);
            }
            for (int i=1; i<=n; i++) aut.CNOT(i, n+i);
            for (int i=n+1; i<=2*n; i++) aut.H(i);
            for (int i=n+1; i<=2*n; i++) aut.X(i);
            if (n >= 3) {
                aut.Toffoli(n+1, n+2, 2*n+2);
                for (int i=3; i<n; i++) // Note that < does not include n!
                    aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
                aut.CZ(3*n-1, 2*n);
                for (int i=n-1; i>=3; i--)
                    aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
                aut.Toffoli(n+1, n+2, 2*n+2);
            } else {
                if (!(n == 2)) throw std::out_of_range("");
                aut.CZ(3, 4);
            }
            for (int i=n+1; i<=2*n; i++) aut.X(i);
            for (int i=n+1; i<=2*n; i++) aut.H(i);
        }
        for (int i=1; i<=n; i++) aut.X(i);
    } else if (type >= 3) { /* Algorithm 3 - Random Circuit */
        if (!(n >= 3)) throw std::out_of_range("");
        aut = VATA::Util::TreeAutomata::classical(n);
        for (int i=0; i<((type==3) ? 6 : 3)*n; i++) {
            int a, b, c;
            switch(rand() % 12) {
                case 0: aut.X(rand_gen()); break;
                case 1: aut.Y(rand_gen()); break;
                case 2: aut.Z(rand_gen()); break;
                case 3: aut.H(rand_gen()); break;
                case 4: aut.S(rand_gen()); break;
                case 5: aut.T(rand_gen()); break;
                case 6: aut.Rx(rand_gen()); break;
                case 7: aut.Ry(rand_gen()); break;
                case 8: rand_gen(a, b); aut.CNOT(a, b); break;
                case 9: rand_gen(a, b); aut.CZ(a, b); break;
                case 10: rand_gen(a, b, c); aut.Toffoli(a, b, c); break;
                case 11: rand_gen(a, b, c); aut.Fredkin(a, b, c); break;
                default: break;
            }
        }
    }
    auto end = chrono::steady_clock::now();
    auto duration = end - start;
    std::cout << n << " & " << aut.qubitNum << " & " << VATA::Util::TreeAutomata::gateCount << " & " << stateBefore << " & " << aut.stateNum << " & " << transitionBefore << " & " << aut.transition_size()
                    << " & " << VATA::Util::TreeAutomata::binop_time * 100 / duration
                    << "\\% & " << VATA::Util::TreeAutomata::branch_rest_time * 100 / duration
                    << "\\% & " << VATA::Util::TreeAutomata::value_rest_time * 100 / duration
                    << "\\% & " << toString(duration) << "\\\\\\hline\n";
    // std::cout << /*n << ": " <<*/ chrono::duration_cast<chrono::milliseconds>(end - start).count() << " & ";
    return 0;
}
