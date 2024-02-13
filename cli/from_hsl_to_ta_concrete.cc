#include "autoq/util/util.hh"
#include "autoq/aut_description.hh"
#include "autoq/parsing/timbuk_parser.hh"
#include <istream>
#include <fstream>

using namespace std;
using AUTOQ::TreeAutomata;
using AUTOQ::Parsing::TimbukParser;

int main(int argc, char **argv) {
try {
    std::string line;
    std::istream *in = &std::cin;
    std::ifstream file;
    if (argc >= 2){
        file.open(argv[1]);
        if (!file) // in case the file could not be open
            throw std::runtime_error(AUTOQ_LOG_PREFIX + "[ERROR] Failed to open file " + std::string(argv[1]) + ".");
        in = &file;
    }
    TreeAutomata aut_final = TimbukParser<TreeAutomata::Symbol>::parse_hsl_from_istream(in);
    aut_final.print();
    return 0;
} catch (std::exception &e) {
    std::cout << e.what() << std::endl;
    return 0;
}
}
