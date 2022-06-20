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

int main(int argc, char **argv) {
    /* Choose exactly one algorithm to run, and comment out the other one. */
    // BV -> let n go from 1 to 10
    // GS -> let n go from 2 to 8
    for (int n=1; n<=10; n++) { // n := the number of qubits
        auto start = chrono::steady_clock::now();

        /* Algorithm 1 - Bernstein-Vazirani */
        VATA::Serialization::TimbukSerializer serializer;
        auto aut = VATA::Util::TreeAutomata::zero(n+1);
        for (int i=1; i<=n+1; i++) {
            aut.H(i);
        }
        aut.Z(n+1);
        for (int i=1; i<=n; i++) {
            auto aut2 = aut;
            aut2.CNOT(i, n+1);
            aut = aut.Union(aut2);
        }
        for (int i=1; i<=n; i++) {
            aut.H(i);
        }
        /************************************/

        /* Algorithm 2 - Grover's Search */
        // assert(n >= 2);
        // auto aut = VATA::Util::TreeAutomata::classical_zero_one_zero(n);
        // for (int i=1; i<=n; i++) aut.X(i);
        // for (int i=n+1; i<=2*n+1; i++) aut.H(i);
        // for (int iter=1; iter <= 1; iter++) { // We modify 
        //     for (int i=1; i<=n; i++) aut.CNOT(i, n+i);
        //     if (n >= 3) {
        //         aut.Toffoli(n+1, n+2, 2*n+2);
        //         for (int i=3; i<=n; i++)
        //             aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
        //         aut.CNOT(3*n, 2*n+1);
        //         for (int i=n; i>=3; i--)
        //             aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
        //         aut.Toffoli(n+1, n+2, 2*n+2);
        //     } else {
        //         assert(n == 2);
        //         aut.Toffoli(3, 4, 5);
        //     }
        //     for (int i=1; i<=n; i++) aut.CNOT(i, n+i);
        //     for (int i=n+1; i<=2*n; i++) aut.H(i);
        //     for (int i=n+1; i<=2*n; i++) aut.X(i);
        //     if (n >= 3) {
        //         aut.Toffoli(n+1, n+2, 2*n+2);
        //         for (int i=3; i<n; i++) // Note that < does not include n!
        //             aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
        //         aut.CZ(3*n-1, 2*n);
        //         for (int i=n-1; i>=3; i--)
        //             aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
        //         aut.Toffoli(n+1, n+2, 2*n+2);
        //     } else {
        //         assert(n == 2);
        //         aut.CZ(3, 4);
        //     }
        //     for (int i=n+1; i<=2*n; i++) aut.X(i);
        //     for (int i=n+1; i<=2*n; i++) aut.H(i);
        // }
        // for (int i=1; i<=n; i++) aut.X(i);
        /*********************************/

        auto end = chrono::steady_clock::now();
        std::cout << n << ": " << chrono::duration_cast<chrono::nanoseconds>(end - start).count() / 1000000
                       << " ms\n";
    }
    return 0;
}
