#include <autoq/util/util.hh>
#include <autoq/aut_description.hh>
#include <autoq/parsing/timbuk_parser.hh>
#include <istream>
#include <fstream>
#include <regex>

using namespace std;
using AUTOQ::Parsing::TimbukParser;
using AUTOQ::PredicateAutomata;

int main(int argc, char **argv) {
try {
    if (argc >= 2 && ((strcmp(argv[1], "-h")==0) || (strcmp(argv[1], "--help")==0))) {
        std::cout << R"(usage: ./paut_from_states [-h] [input.txt]

positional arguments:
  input.txt             the input high-level specification language
                        If this file is not provided, the user should provide the language
                        via stdin.


optional arguments:
  -h, --help            show this help message and exit)" << std::endl;
        return 0;
    }
    PredicateAutomata aut_final;
    std::string line;
    std::istream *in = &std::cin;
    std::ifstream file;
    if (argc >= 2){
        file.open(argv[1]);
        if (!file) // in case the file could not be open
            throw std::runtime_error("[ERROR] Failed to open file " + std::string(argv[1]) + ".");
        in = &file;
    }
    while (std::getline(*in, line)) {
        line = AUTOQ::Util::trim(line);
        if (line.substr(0, 4) == "|i|=") { // if startswith "|i|="
            std::istringstream iss(line);
            std::string length; iss >> length; length = length.substr(4);
            line.clear();
            for (std::string t; iss >> t;)
                line += t + ' ';
            std::string i(std::atoi(length.c_str()), '1');
            bool reach_all_zero;
            do {
                auto aut = TimbukParser<typename PredicateAutomata::Symbol>::from_line_to_automaton(std::regex_replace(line, std::regex("i:"), i + ":"));
                aut_final = aut_final || aut;
                aut_final.reduce();

                // the following performs -1 on the binary string i
                reach_all_zero = false;
                for (int j=i.size()-1; j>=0; j--) {
                    if (i.at(j) == '0') {
                        if (j == 0) {
                            reach_all_zero = true;
                            break;
                        }
                        i.at(j) = '1';
                    } else {
                        i.at(j) = '0';
                        break;
                    }
                }
            } while (!reach_all_zero);
        } else {
            auto aut = TimbukParser<typename PredicateAutomata::Symbol>::from_line_to_automaton(line);
            aut_final = aut_final || aut;
            aut_final.reduce();
        }
    }
    aut_final.reduce();
    std::cout << std::endl;
    aut_final.print_aut();
    return 0;
} catch (std::exception &e) {
    std::cout << e.what() << std::endl;
    return 0;
}
}