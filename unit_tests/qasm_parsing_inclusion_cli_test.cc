/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Description:
 *    Tests for QASM parsing, inclusion checker, and CLI (subprocess)
 *
 *****************************************************************************/

#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE QasmParsingInclusionCli
#include <boost/test/unit_test.hpp>

#include <cstdlib>
#include <fstream>
#include <sstream>
#include <string>
#include <utility>
#include <vector>
#include <sys/wait.h>
#include <unistd.h>

#include "autoq/symbol/concrete.hh"
#include "autoq/complex/complex.hh"
#include "autoq/parsing/parser/timbuk_parser.hh"
#include "autoq/serialization/timbuk_serializer.hh"
#include "autoq/inclusion.hh"
#include "test_util.hh"

using AUTOQ::Complex::Complex;
using AUTOQ::Symbol::Concrete;

struct Fixture {
    Fixture() {
        if constexpr (std::is_same_v<AUTOQ::Complex::Complex, AUTOQ::Complex::nTuple>) {
            AUTOQ::Complex::nTuple::N = 4;
        }
    }
};
BOOST_TEST_GLOBAL_FIXTURE(Fixture);

BOOST_AUTO_TEST_CASE(qasm_parsing_minimal_circuit)
{
    std::string folder = test_dir_from_file(__FILE__, "testcase/GroverFor/");
    std::string pre = folder + "pre.hsl";
    std::string post = folder + "post.hsl";
    std::string circuit = folder + "circuit.qasm";

    auto [autVec, qp] = AUTOQ::Parsing::TimbukParser<Concrete>::ReadTwoAutomata(pre, post, circuit);
    auto aut = autVec.at(0);
    auto spec = autVec.at(1);
    autVec.erase(autVec.begin(), autVec.begin() + 2);

    bool ok = aut.execute(circuit, qp, autVec, {});
    BOOST_REQUIRE_MESSAGE(ok, "QASM execution failed for " + circuit);

    bool included = (aut <<= spec);
    BOOST_REQUIRE_MESSAGE(included, "Inclusion check failed after QASM parsing:\n"
        + AUTOQ::Serialization::TimbukSerializer::Serialize(aut)
        + AUTOQ::Serialization::TimbukSerializer::Serialize(spec));
}

BOOST_AUTO_TEST_CASE(inclusion_checker_equal_automata)
{
    auto aut = AUTOQ::ConcreteAutomata::basis(3);
    auto spec = aut;
    BOOST_REQUIRE(aut <<= spec);
    BOOST_REQUIRE(spec <<= aut);
}

#ifndef AUTOQ_CLI_PATH
#define AUTOQ_CLI_PATH "autoq"
#endif

BOOST_AUTO_TEST_CASE(cli_subprocess_verification)
{
    std::string folder = test_dir_from_file(__FILE__, "../benchmarks/all/BV/03/");
    std::string pre = folder + "pre.hsl";
    std::string post = folder + "post.hsl";
    std::string circuit = folder + "circuit.qasm";

    std::ostringstream cmd;
    cmd << AUTOQ_CLI_PATH << " ver \"" << pre << "\" \"" << circuit << "\" \"" << post << "\"";
    std::string cmd_str = cmd.str();

    int status = std::system(cmd_str.c_str());
    int exit_code = WEXITSTATUS(status);
    BOOST_REQUIRE_MESSAGE(exit_code == 0, "CLI verification failed (exit " + std::to_string(exit_code) + "): " + cmd_str);
}

// Runs the CLI through the shell and returns its exit status together with
// its combined stdout and stderr. A crash shows up as 128 + the signal number
// (134 for an abort).
static std::pair<int, std::string> run_cli(const std::string& args)
{
    std::string cmd = std::string(AUTOQ_CLI_PATH) + " " + args + " 2>&1";
    FILE* pipe = popen(cmd.c_str(), "r");
    BOOST_REQUIRE_MESSAGE(pipe, "popen failed: " + cmd);
    std::string output;
    char buffer[512];
    while (fgets(buffer, sizeof(buffer), pipe) != nullptr)
        output += buffer;
    int status = pclose(pipe);
    return {WIFEXITED(status) ? WEXITSTATUS(status) : -1, output};
}

// Malformed input must be reported as "[ERROR] ..." with exit status 1, not
// abort the process (#56, #37, #38).
BOOST_AUTO_TEST_CASE(cli_malformed_input_is_reported)
{
    std::string dir = test_dir_from_file(__FILE__, "testcase/MalformedInput/");
    auto f = [&](const std::string& name) { return "\"" + dir + name + "\""; };
    const std::vector<std::pair<std::string, std::string>> cases = {
        {"ex " + f("pre.hsl") + " " + f("if_undef.qasm"), "The if guard variable \"d[0]\""},
        {"ex " + f("pre.hsl") + " " + f("if_empty.qasm"), "Empty if guard"},
        {"ex " + f("pre.hsl") + " " + f("while_undef.qasm"), "The while guard variable \"d[0]\""},
        {"ex " + f("pre.hsl") + " " + f("for_notype.qasm"), "Unsupported for-loop header"},
        {"ex " + f("pre.hsl") + " " + f("for_big.qasm"), "are too large"},
        {"ex " + f("pre.hsl") + " " + f("rx_bad.qasm"), "Division by zero"},
        {"print " + f("div0.hsl"), "Division by zero"},
        {"eq " + f("eq_big.qasm") + " " + f("eq_big.qasm"), "is too large"},
        // Not validated yet (#33); the generic handler in main reports it.
        {"print " + f("eipi_symbolic.hsl"), "[ERROR] "},
    };
    for (const auto& [args, expected] : cases) {
        auto [code, output] = run_cli(args);
        BOOST_CHECK_MESSAGE(code == 1, args + ": exit status " + std::to_string(code) + ", output: " + output);
        BOOST_CHECK_MESSAGE(output.find(expected) != std::string::npos,
            args + ": expected \"" + expected + "\" in output: " + output);
    }
}

// OpenQASM 3 allows whitespace between ! and its operand (#38).
BOOST_AUTO_TEST_CASE(cli_negated_guard_with_space)
{
    std::string dir = test_dir_from_file(__FILE__, "testcase/MalformedInput/");
    auto [code, output] = run_cli("ex \"" + dir + "pre.hsl\" \"" + dir + "if_space_not.qasm\"");
    BOOST_CHECK_MESSAGE(code == 0, "exit status " + std::to_string(code) + ", output: " + output);
    BOOST_CHECK_MESSAGE(output.find("(1/1)|1>") != std::string::npos, "unexpected output: " + output);
}
