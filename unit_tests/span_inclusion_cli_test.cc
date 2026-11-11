#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE SpanInclusionCli
#include <boost/test/unit_test.hpp>

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>
#include <sys/wait.h>

#include "span_test_util.hh"

#ifndef AUTOQ_CLI_PATH
#define AUTOQ_CLI_PATH "autoq"
#endif

namespace {

int run_cmd(const std::string &cmd) {
    const int status = std::system(cmd.c_str());
    if (status == -1) {
        return -1;
    }
    return WEXITSTATUS(status);
}

std::string quote(const std::string &s) {
    return "\"" + s + "\"";
}

std::filesystem::path make_temp_dir() {
    const auto dir = std::filesystem::temp_directory_path() / "autoq_span_cli_tests";
    std::filesystem::create_directories(dir);
    return dir;
}

}  // namespace

BOOST_AUTO_TEST_CASE(span_inclusion_cli_reports_included)
{
    const auto dir = make_temp_dir();
    const auto a = span_test::automaton_from_vectors(1, {{1, 1}});
    const auto b = span_test::automaton_from_vectors(1, {{1, 0}, {0, 1}});

    const auto a_path = (dir / "included_A.aut").string();
    const auto b_path = (dir / "included_B.aut").string();
    span_test::write_automaton_file(a, a_path);
    span_test::write_automaton_file(b, b_path);

    std::ostringstream cmd;
    cmd << AUTOQ_CLI_PATH << " span-inclusion " << quote(a_path) << " " << quote(b_path) << " --qubits 1";
    BOOST_TEST(run_cmd(cmd.str()) == 0);
}

BOOST_AUTO_TEST_CASE(span_inclusion_cli_reports_not_included)
{
    const auto dir = make_temp_dir();
    const auto a = span_test::automaton_from_vectors(1, {{1, 0}, {0, 1}});
    const auto b = span_test::automaton_from_vectors(1, {{1, 1}});

    const auto a_path = (dir / "notincluded_A.aut").string();
    const auto b_path = (dir / "notincluded_B.aut").string();
    span_test::write_automaton_file(a, a_path);
    span_test::write_automaton_file(b, b_path);

    std::ostringstream cmd;
    cmd << AUTOQ_CLI_PATH << " span-inclusion " << quote(a_path) << " " << quote(b_path) << " --qubits 1";
    BOOST_TEST(run_cmd(cmd.str()) == 2);
}

BOOST_AUTO_TEST_CASE(span_inclusion_cli_reports_resource_limit)
{
    const auto dir = make_temp_dir();
    const auto a = span_test::automaton_from_vectors(1, {{1, 1}});
    const auto b = span_test::automaton_from_vectors(1, {{1, 0}, {0, 1}});

    const auto a_path = (dir / "resource_A.aut").string();
    const auto b_path = (dir / "resource_B.aut").string();
    span_test::write_automaton_file(a, a_path);
    span_test::write_automaton_file(b, b_path);

    std::ostringstream cmd;
    cmd << AUTOQ_CLI_PATH << " span-inclusion " << quote(a_path) << " " << quote(b_path)
        << " --qubits 1 --max-basis-runs 1";
    BOOST_TEST(run_cmd(cmd.str()) == 3);
}
