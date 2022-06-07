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
    /* Initialize aut. */
    int n = 3;
    TreeAutomata aut = TreeAutomata::zero(n+1);
    for (int i=1; i<=n+1; i++) {
        auto start = chrono::steady_clock::now();
        aut.H(i);
        auto end = chrono::steady_clock::now();
        aut.print();
        std::cout << "H" << i << " Elapsed time: " << std::setw(5)
        << chrono::duration_cast<chrono::nanoseconds>(end - start).count() / 1000000
        << " ms\n\n";
    }
    auto start = chrono::steady_clock::now();
    aut.Z(n+1);
    auto end = chrono::steady_clock::now();
    aut.print();
    std::cout << "Z Elapsed time: " << std::setw(5)
    << chrono::duration_cast<chrono::nanoseconds>(end - start).count() / 1000000
    << " ms\n\n";
    for (int i=1; i<=n; i++) {
        TreeAutomata aut2 = aut;
        auto start = chrono::steady_clock::now();
        aut2.CNOT(i, n+1);
        auto end = chrono::steady_clock::now();
        aut.print();
        std::cout << "CNOT" << i << " Elapsed time: " << std::setw(5)
        << chrono::duration_cast<chrono::nanoseconds>(end - start).count() / 1000000
        << " ms\n\n";

        start = chrono::steady_clock::now();
        aut = aut.Union(aut2);
        end = chrono::steady_clock::now();
        aut.print();
        std::cout << "Union" << i << " Elapsed time: " << std::setw(5)
        << chrono::duration_cast<chrono::nanoseconds>(end - start).count() / 1000000
        << " ms\n\n";
    }
    for (int i=1; i<=n; i++) {
        auto start = chrono::steady_clock::now();
        if (i == 1)
            aut.name = "TARGET";
        else
            aut.name = "****";
        aut.H(i);
        auto end = chrono::steady_clock::now();
        aut.print();
        std::cout << "H" << i <<" Elapsed time: " << std::setw(5)
        << chrono::duration_cast<chrono::nanoseconds>(end - start).count() / 1000000
        << " ms\n\n";
    }
    // if (argc == 2) {
    //     TimbukParser parser;
    //     aut = parser.ParseString(ReadFile(argv[1]));
    // } else {
    //     // aut = TreeAutomata::uniform(3);
    //     aut = TreeAutomata::classical(3);
    // }
    // // aut.determinize();
    // // aut.minimize();

    // TimbukSerializer serializer;
    // ofstream file1("/tmp/automata1.txt");
    // file1 << serializer.Serialize(aut);
    // file1.close();

    // /* Perform any operation here. */
    // aut.CNOT(1,2);
    // // aut.determinize();
    // // aut.minimize();
    // ofstream file2("/tmp/automata2.txt");
    // file2 << serializer.Serialize(aut);
    // file2.close();

    // string include1, include2;
    // ShellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata1.txt /tmp/automata2.txt", include1);
    // ShellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata2.txt /tmp/automata1.txt", include2);
    // assert(!(include1=="1\n" && include2=="1\n"));
    // // return 0;

    // aut.CNOT(1,2);
    // // aut.determinize();
    // // aut.minimize();
    // /* Output this automata. */
    // // cout << serializer.Serialize(aut);
    // ofstream file3("/tmp/automata2.txt");
    // file3 << serializer.Serialize(aut);
    // file3.close();

    // /* Compare the two automata. */
    // ShellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata1.txt /tmp/automata2.txt", include1);
    // ShellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata2.txt /tmp/automata1.txt", include2);
    // std::cout << include1 << include2;
    // assert(include1=="1\n" && include2=="1\n");
    return 0;
}