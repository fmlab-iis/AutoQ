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

int main (int argc, char **argv) {
    auto before0 = ReadAutomaton(argv[1]);
    std::visit([](auto&& arg) {
        arg.reduce();
        arg.print_aut("After Reduce:\n");
    }, before0);
    return 0;
}