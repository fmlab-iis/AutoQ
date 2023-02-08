#include <autoq/util/aut_description.hh>
#include <autoq/parsing/timbuk_parser.hh>

using namespace std;
using AUTOQ::Util::TreeAutomata;
using AUTOQ::Parsing::TimbukParser;

int main(int argc, char **argv) {
    std::string aut;
    std::getline(std::cin, aut, static_cast<char>(EOF)); // contains multiple lines!
    TimbukParser<AUTOQ::Util::TreeAutomata::InitialSymbol>::ParseString(aut).print_language();
    return 0;
}