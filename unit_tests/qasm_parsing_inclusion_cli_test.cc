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
#include <sys/wait.h>
#include <unistd.h>

#include "autoq/symbol/concrete.hh"
#include "autoq/complex/complex.hh"
#include "autoq/parsing/parser/timbuk_parser.hh"
#include "autoq/serialization/timbuk_serializer.hh"
#include "autoq/inclusion.hh"

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
    std::string base(__FILE__);
    base = base.substr(0, base.find_last_of("\\/"));
    std::string folder = base + "/testcase/GroverFor/";
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
    auto aut = AUTOQ::TreeAutomata::basis(3);
    auto spec = aut;
    BOOST_REQUIRE(aut <<= spec);
    BOOST_REQUIRE(spec <<= aut);
}

#ifndef AUTOQ_CLI_PATH
#define AUTOQ_CLI_PATH "autoq"
#endif

BOOST_AUTO_TEST_CASE(cli_subprocess_verification)
{
    std::string base(__FILE__);
    base = base.substr(0, base.find_last_of("\\/"));
    std::string folder = base + "/../benchmarks/all/BV/03/";
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
