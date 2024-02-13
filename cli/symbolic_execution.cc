#include "autoq/parsing/timbuk_parser.hh"

int main(int argc, char **argv) {
try {
    auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadAutomaton(argv[1]);
    aut.execute(argv[2]);
    aut.fraction_simplification();
    aut.remove_useless();
    aut.reduce();
    aut.print_language();
    return 0;
} catch (std::exception &e) {
    std::cout << e.what() << std::endl;
    return 0;
}
}