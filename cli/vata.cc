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
    for (int n=1; n<=100; n++) {
        auto start = chrono::steady_clock::now();

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

        // assert(n >= 2);
        // auto aut = VATA::Util::TreeAutomata::classical_zero_one_zero(n);

        // /********************************/
        // for (int i=1; i<=n; i++) aut.X(i);
        // for (int i=n+1; i<=2*n+1; i++) aut.H(i);
        // /**************************************/

        // for (int iter=1; iter <= M_PI / (4 * asin(1 / pow(2, n/2.0))); iter++) {
        //     /****************************************/
        //     for (int i=1; i<=n; i++) aut.CNOT(i, n+i);
        //     /* multi-controlled NOT gate */
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
        //     /*****************************/
        //     for (int i=1; i<=n; i++) aut.CNOT(i, n+i);
        //     /****************************************/

        //     /************************************/
        //     for (int i=n+1; i<=2*n; i++) aut.H(i);
        //     for (int i=n+1; i<=2*n; i++) aut.X(i);
        //     /* multi-controlled Z gate */
        //     if (n >= 3) {
        //         aut.Toffoli(n+1, n+2, 2*n+2);
        //         for (int i=3; i<n; i++) // Note that < does not include n!
        //             aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
        //         aut.CZ(3*n-1, 2*n);
        //         for (int i=n-1; i>=3; i--)
        //             aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
        //         aut.Toffoli(n+1, n+2, 2*n+2);
        //     // } else if (n == 3) {
        //     //     aut.H(2*n);
        //     //     aut.Toffoli(4, 5, 6);
        //     //     aut.H(2*n);
        //     } else {
        //         assert(n == 2);
        //         aut.CZ(3, 4);
        //     }
        //     /***************************/
        //     for (int i=n+1; i<=2*n; i++) aut.X(i);
        //     for (int i=n+1; i<=2*n; i++) aut.H(i);
        //     /************************************/
        // }

        // /********************************/
        // for (int i=1; i<=n; i++) aut.X(i);
        // /********************************/
        auto end = chrono::steady_clock::now();
        std::cout << n << ": " << chrono::duration_cast<chrono::nanoseconds>(end - start).count() / 1000000
                       << " ms\n";
    }
    // /* bug production */
    // int size = 2;
    // for (const auto &before : {VATA::Util::TreeAutomata::classical(size)}) {
    //     VATA::Util::TreeAutomata after = before;
    //     int loop = 2;
    //     for (int i=0; i<loop; i++) {
    //         after.CZ(size*2/3, size/3);
    //     }
    // }
    // return 0;

    // bool print = true;

    // for (int n=5; n<=5; n++) {
    // /* Initialize aut. */
    // auto start2 = chrono::steady_clock::now();
    // TreeAutomata aut = TreeAutomata::zero(n+1);
    // aut.name = "TARGET";
    // aut.H(1);
    // // if (print) {
    // //     aut.print();
    // // }
    // return 0;
    // for (int i=1; i<=n+1; i++) {
    //     auto start = chrono::steady_clock::now();
    //     aut.H(i);
    //     auto end = chrono::steady_clock::now();
    //     if (print) {
    //         aut.print();
    //         std::cout << "H" << i << " Elapsed time: " << std::setw(5)
    //         << chrono::duration_cast<chrono::nanoseconds>(end - start).count() / 1000000
    //         << " ms\n\n";
    //     }
    // }
    // auto start = chrono::steady_clock::now();
    // aut.Z(n+1);
    // auto end = chrono::steady_clock::now();
    // if (print) {
    //     aut.print();
    //     std::cout << "Z Elapsed time: " << std::setw(5)
    //     << chrono::duration_cast<chrono::nanoseconds>(end - start).count() / 1000000
    //     << " ms\n\n";
    // }
    // for (int i=1; i<=n; i++) {
    //     TreeAutomata aut2 = aut;
    //     auto start = chrono::steady_clock::now();
    //     aut2.CNOT(i, n+1);
    //     auto end = chrono::steady_clock::now();
    //     if (print) {
    //         aut.print();
    //         std::cout << "CNOT" << i << " Elapsed time: " << std::setw(5)
    //         << chrono::duration_cast<chrono::nanoseconds>(end - start).count() / 1000000
    //         << " ms\n\n";
    //     }
    //     start = chrono::steady_clock::now();
    //     aut = aut.Union(aut2);
    //     end = chrono::steady_clock::now();
    //     if (print) {
    //         aut.print();
    //         std::cout << "Union" << i << " Elapsed time: " << std::setw(5)
    //         << chrono::duration_cast<chrono::nanoseconds>(end - start).count() / 1000000
    //         << " ms\n\n";
    //     }
    // }
    // for (int i=1; i<=n; i++) {
    //     auto start = chrono::steady_clock::now();
    //     aut.H(i);
    //     auto end = chrono::steady_clock::now();
    //     if (print) {
    //         aut.print();
    //         std::cout << "H" << i <<" Elapsed time: " << std::setw(5)
    //         << chrono::duration_cast<chrono::nanoseconds>(end - start).count() / 1000000
    //         << " ms\n\n";
    //     }
    // }
    // auto end2 = chrono::steady_clock::now();
    // std::cout << "(" << n << ") Elapsed time: " << std::setw(10)
    // << chrono::duration_cast<chrono::nanoseconds>(end2 - start2).count() / 1000000
    // << " ms\n";
    // std::cout << "=============================\n";
    // }
    // // if (argc == 2) {
    // //     TimbukParser parser;
    // //     aut = parser.ParseString(ReadFile(argv[1]));
    // // } else {
    // //     // aut = TreeAutomata::uniform(3);
    // //     aut = TreeAutomata::classical(3);
    // // }
    // // aut.determinize();
    // // aut.minimize();

    // // /* Perform any operation here. */
    // // aut.CNOT(1,2);
    // // // aut.determinize();
    // // // aut.minimize();
    // // ofstream file2("/tmp/automata2.txt");
    // // file2 << serializer.Serialize(aut);
    // // file2.close();

    // // string include1, include2;
    // // ShellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata1.txt /tmp/automata2.txt", include1);
    // // ShellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata2.txt /tmp/automata1.txt", include2);
    // // assert(!(include1=="1\n" && include2=="1\n"));
    // // // return 0;

    // // aut.CNOT(1,2);
    // // // aut.determinize();
    // // // aut.minimize();
    // // /* Output this automata. */
    // // // cout << serializer.Serialize(aut);
    // // ofstream file3("/tmp/automata2.txt");
    // // file3 << serializer.Serialize(aut);
    // // file3.close();

    // // /* Compare the two automata. */
    // // ShellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata1.txt /tmp/automata2.txt", include1);
    // // ShellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata2.txt /tmp/automata1.txt", include2);
    // // std::cout << include1 << include2;
    // // assert(include1=="1\n" && include2=="1\n");
    return 0;
}
