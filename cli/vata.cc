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
    assert(argc == 2);

    TimbukParser parser;
    TreeAutomata aut = parser.ParseString(ReadFile(argv[1]));

    // aut.minimize();

    TimbukSerializer serializer;
    std::cout << serializer.Serialize(aut);
    return 0;
}