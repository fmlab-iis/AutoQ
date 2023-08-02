#include <autoq/aut_description.hh>
#include <autoq/parsing/timbuk_parser.hh>

using namespace std;
using AUTOQ::TreeAutomata;
using AUTOQ::Parsing::TimbukParser;

int main(int argc, char **argv) {
    std::string aut;
    std::getline(std::cin, aut, static_cast<char>(EOF)); // contains multiple lines!
    TimbukParser<AUTOQ::TreeAutomata::Symbol>::ParseString(aut).print_language();
    return 0;
}