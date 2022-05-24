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
        aut.determinize();
        aut.minimize();
    } else {
        // aut = TreeAutomata::uniform(5);
        // aut = TreeAutomata::classical(5);
    }
    
    /* Perform any operation here. */
    aut.Z(1);
    aut.Z(1);

    /* Output this automata. */
    TimbukSerializer serializer;
    cout << serializer.Serialize(aut);

    /* Compare the two automata. */
    // string include1, include2;
    // ShellCmd(path_to_VATA + " incl /tmp/automata1.txt /tmp/automata2.txt", include1);
    // ShellCmd(path_to_VATA + " incl /tmp/automata2.txt /tmp/automata1.txt", include2);
    // assert(include1=="1\n" && include1=="2\n");
    return 0;
}