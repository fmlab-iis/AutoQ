#include "autoq/aut_description.hh"
#include "autoq/parsing/timbuk_parser.hh"

using namespace std;
using AUTOQ::TreeAutomata;
using AUTOQ::Parsing::TimbukParser;

int main(int, char **argv) {
    // std::string aut;
    // std::getline(std::cin, aut, static_cast<char>(EOF)); // contains multiple lines!
    TimbukParser<AUTOQ::TreeAutomata::Symbol>::ReadAutomaton(argv[1]).print_language();
    return 0;
}