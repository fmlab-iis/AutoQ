#include <fstream>
#include <iostream>
#include <vata/parsing/timbuk_parser.hh>
#include <vata/serialization/timbuk_serializer.hh>
#include <vata/util/aut_description.hh>
#include <vata/util/util.hh>

using namespace std;
using VATA::Parsing::TimbukParser;
using VATA::Serialization::TimbukSerializer;
using VATA::Util::TreeAutomata;
using VATA::Util::ShellCmd;
using VATA::Util::ReadFile;

int main(int argc, char **argv) {
    
    /* Initialize aut. */
    TreeAutomata aut;
    if (argc == 2) {
        TimbukParser parser;
        aut = parser.ParseString(ReadFile(argv[1]));
    } else {
        aut = TreeAutomata::uniform(1);
        // aut = TreeAutomata::classical(1);
    }
    // aut.determinize();
    // aut.minimize();

    TimbukSerializer serializer;
    ofstream file1("/tmp/automata1.txt");
    file1 << serializer.Serialize(aut);
    file1.close();

    /* Perform any operation here. */
    aut.Rx(1);
    // aut.determinize();
    // aut.minimize();
    ofstream file2("/tmp/automata2.txt");
    file2 << serializer.Serialize(aut);
    file2.close();

    string include1, include2;
    ShellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata1.txt /tmp/automata2.txt", include1);
    ShellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata2.txt /tmp/automata1.txt", include2);
    assert(!(include1=="1\n" && include2=="1\n"));
    // return 0;

    aut.Rx(1);
    aut.Rx(1);
    aut.Rx(1);
    aut.Rx(1);
    aut.Rx(1);
    aut.Rx(1);
    aut.Rx(1);
    // aut.determinize();
    // aut.minimize();
    /* Output this automata. */
    // cout << serializer.Serialize(aut);
    ofstream file3("/tmp/automata2.txt");
    file3 << serializer.Serialize(aut);
    file3.close();

    /* Compare the two automata. */
    ShellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata1.txt /tmp/automata2.txt", include1);
    ShellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata2.txt /tmp/automata1.txt", include2);
    std::cout << include1 << include2;
    assert(include1=="1\n" && include2=="1\n");
    return 0;
}