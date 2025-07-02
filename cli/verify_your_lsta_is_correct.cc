#include <fstream>
#include <iostream>
#include <autoq/error.hh>
#include <autoq/parsing/timbuk_parser.hh>
#include <autoq/parsing/complex_parser.hh>
#include <autoq/serialization/timbuk_serializer.hh>
#include <autoq/aut_description.hh>
#include <autoq/inclusion.hh>
#include <autoq/util/util.hh>
#include <autoq/util/string.hh>
#include <autoq/complex/ntuple.hh>
#include <autoq/complex/complex.hh>
#include <sys/wait.h>
#include <unistd.h>
#include <chrono>
#include <iomanip>
#include <regex>
#include <fenv.h>
#include <csignal>
#include <fenv_darwin.h>
#include <CLI11.hpp>

using namespace std;

int main(int argc, char **argv) {
try {
    CLI::App app{"AutoQ: An automata-based C++ tool for quantum program verification."};
    std::string file1, file2;
    app.add_option("file1", file1, "file1")->required()->type_name("");
    app.add_option("file2", file2, "file2")->required()->type_name("");
    CLI11_PARSE(app, argc, argv); // Parse the command-line arguments
    auto aut1 = ReadAutomaton(file1);
    auto aut2 = ReadAutomaton(file2);
    std::visit([](auto& aut){
        aut.print_language("=============================\nfile 1:\n");
        std::cout << "=============================" << std::endl;
    }, aut1);
    std::visit([](auto& aut){
        aut.print_language("file 2:\n");
        std::cout << "=============================" << std::endl;
    }, aut2);
    if ((aut1 <= aut2) && (aut2 <= aut1)) {
        std::cout << "😀" << std::endl;
    } else {
        std::cout << "🥹" << std::endl;
    }
} catch (AutoQError &e) {
    std::cout << e.what() << std::endl;
}
    return 0;
}
