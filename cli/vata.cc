#include <iostream>
#include <vata/parsing/timbuk_parser.hh>
#include <vata/serialization/timbuk_serializer.hh>
#include <vata/util/aut_description.hh>
#include <vata/util/util.hh>

using namespace std;
using VATA::Parsing::TimbukParser;
using VATA::Serialization::TimbukSerializer;
using VATA::Util::TreeAutomata;
using VATA::Util::ReadFile;

int main(int argc, char **argv) {
    assert(argc == 3);

    TimbukParser parser;
    TreeAutomata aut = parser.ParseString(ReadFile(argv[2]));
    aut.determinize();
    aut.semi_determinize();

    for (int i=0; i<8; i++) {
        TreeAutomata aut2 = aut;
        aut.branch_restriction(1, false);
        aut2.branch_restriction(1);
        aut2.omega_multiplication();
        // aut2.omega_multiplication();
        aut = aut + aut2;
    }
    aut.semi_undeterminize();
    // aut.determinize();
    // aut.minimize();

    if (strcmp(argv[1], "load") == 0) {}
    else if (strcmp(argv[1], "red") == 0) {
        aut.minimize();
    }

    TimbukSerializer serializer;
    std::cout << serializer.Serialize(aut);
    return 0;
}