#include <autoq/aut_description.hh>
#include <autoq/parsing/timbuk_parser.hh>

using namespace std;
using AUTOQ::TreeAutomata;
using AUTOQ::Parsing::TimbukParser;

int main(int argc, char **argv) {
    AUTOQ::TreeAutomata aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(argv[1]);
    aut.print_language();
    return 0;
}
