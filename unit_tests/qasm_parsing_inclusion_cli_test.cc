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

#include <fstream>
#include <string>
#include <utility>
#include <vector>
#include <sys/wait.h>
#include <unistd.h>

#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
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

// Kets for the same qubits must have the same length; otherwise parsing
// reports an AutoQError instead of aborting with std::out_of_range (#34).
BOOST_AUTO_TEST_CASE(misaligned_kets_are_rejected)
{
    std::string folder = test_dir_from_file(__FILE__, "testcase/KetAlignment/");
    using Parser = AUTOQ::Parsing::TimbukParser<Concrete>;
    for (const std::string f : {"shorter_ket.hsl", "longer_ket.hsl", "ket_ends_inside_constant.hsl"})
        BOOST_CHECK_THROW(Parser::ReadAutomaton(folder + f), AutoQError);
    BOOST_CHECK_THROW(Parser::ReadTwoAutomata(folder + "pre.hsl", folder + "post_shorter.hsl", folder + "circuit.qasm"), AutoQError);

    BOOST_CHECK_NO_THROW(Parser::ReadAutomaton(folder + "aligned.hsl"));
    BOOST_CHECK_NO_THROW(Parser::ReadTwoAutomata(folder + "pre.hsl", folder + "post.hsl", folder + "circuit.qasm"));
}

// A character the HSL lexer does not recognise must be a parse error.
// ANTLR's default lexer listener drops it and continues, so 1/√2 was read as 1/2 (#25).
BOOST_AUTO_TEST_CASE(lexer_rejects_unknown_characters)
{
    std::string folder = test_dir_from_file(__FILE__, "testcase/LexerError/");
    using Parser = AUTOQ::Parsing::TimbukParser<Concrete>;
    BOOST_CHECK_THROW(Parser::ReadAutomaton(folder + "sqrt_char.hsl"), AutoQError);
    BOOST_CHECK_THROW(Parser::ReadAutomaton(folder + "const_sqrt_char.hsl"), AutoQError);
    BOOST_CHECK_NO_THROW(Parser::ReadAutomaton(folder + "sqrt2.hsl"));
}

// "Root" and "States" in the header are not state names. A state that is
// actually called States or Root must not become an extra root, and a root
// name that no transition mentions is an error (#31).
BOOST_AUTO_TEST_CASE(lsta_root_header_is_not_a_state_name)
{
    std::string folder = test_dir_from_file(__FILE__, "testcase/LstaRoot/");
    using Parser = AUTOQ::Parsing::TimbukParser<Concrete>;
    auto named_states = Parser::ReadAutomaton(folder + "pre_states.lsta");
    auto named_root = Parser::ReadAutomaton(folder + "pre_root.lsta");
    auto control = Parser::ReadAutomaton(folder + "pre_s.lsta");
    BOOST_REQUIRE_EQUAL(named_states.finalStates.size(), 1u);
    BOOST_REQUIRE_EQUAL(named_root.finalStates.size(), 1u);
    BOOST_REQUIRE(named_states.finalStates == control.finalStates);
    BOOST_REQUIRE(named_root.finalStates == control.finalStates);
    BOOST_REQUIRE(named_states <<= control);
    BOOST_REQUIRE(control <<= named_states);
    BOOST_REQUIRE(named_root <<= control);
    BOOST_REQUIRE(control <<= named_root);
    BOOST_CHECK_THROW(Parser::ReadAutomaton(folder + "pre_typo.lsta"), AutoQError);
    BOOST_CHECK_NO_THROW(Parser::ReadAutomaton(test_dir_from_file(__FILE__, "testcase/EmptyAutomaton/zero.lsta")));
}

// A // comment ends at the newline. Deleting that newline joins the next line
// onto this one, so a constant, a section header, or a constraint is parsed
// together with whatever follows (#28). A comment-only line is still removed
// whole, so it does not become a blank line in Constraints.
BOOST_AUTO_TEST_CASE(trailing_line_comment_does_not_join_the_next_line)
{
    std::string folder = test_dir_from_file(__FILE__, "testcase/LineComment/");
    using ConcreteParser = AUTOQ::Parsing::TimbukParser<Concrete>;
    using SymbolicParser = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>;

    auto equivalent = [](const auto& commented, const auto& control, const std::string& name) {
        BOOST_CHECK_MESSAGE(commented <<= control, name + ": commented automaton is not included in the control");
        BOOST_CHECK_MESSAGE(control <<= commented, name + ": control is not included in the commented automaton");
    };

    equivalent(ConcreteParser::ReadAutomaton(folder + "pre.hsl"),
               ConcreteParser::ReadAutomaton(folder + "pre_ctrl.hsl"), "constant");
    equivalent(ConcreteParser::ReadAutomaton(folder + "a.hsl"),
               ConcreteParser::ReadAutomaton(folder + "a_ctrl.hsl"), "header");
    equivalent(ConcreteParser::ReadAutomaton(folder + "b1.hsl"),
               ConcreteParser::ReadAutomaton(folder + "b1_ctrl.hsl"), "fraction");

    auto [autVec, qp] = ConcreteParser::ReadTwoAutomata(folder + "pre.hsl", folder + "post.hsl", folder + "circuit.qasm");
    auto aut = autVec.at(0);
    auto spec = autVec.at(1);
    BOOST_REQUIRE(aut.execute(folder + "circuit.qasm", qp));
    BOOST_CHECK(aut <<= spec);

    auto commented = SymbolicParser::ReadAutomaton(folder + "c.hsl");
    auto control = SymbolicParser::ReadAutomaton(folder + "c_ctrl.hsl");
    auto comment_line = SymbolicParser::ReadAutomaton(folder + "c_line.hsl");
    BOOST_CHECK_EQUAL(commented.constraints, control.constraints);
    BOOST_CHECK_EQUAL(comment_line.constraints, control.constraints);
    equivalent(commented, control, "constraint");
    equivalent(comment_line, control, "comment-only constraint");

    auto [symVec, sqp] = SymbolicParser::ReadTwoAutomata(folder + "c.hsl", folder + "post.hsl", folder + "circuit.qasm");
    auto symbolic = symVec.at(0);
    auto symbolic_spec = symVec.at(1);
    BOOST_REQUIRE(symbolic.execute(folder + "circuit.qasm", sqp));
    BOOST_CHECK(symbolic <<= symbolic_spec);
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

// ver exits 0 for both [OK] and [failed], so the exit code alone cannot tell
// them apart. This test has to see the verdict (#44).
BOOST_AUTO_TEST_CASE(cli_subprocess_verification)
{
    std::string folder = test_dir_from_file(__FILE__, "../benchmarks/all/BV/03/");
    auto [code, output] = run_cli("ver \"" + folder + "pre.hsl\" \"" + folder + "circuit.qasm\" \"" + folder + "post.hsl\"");
    BOOST_REQUIRE_MESSAGE(code == 0, "CLI did not exit 0 (status " + std::to_string(code) + "):\n" + output);
    BOOST_REQUIRE_MESSAGE(output.find("The verification process [OK]") != std::string::npos,
        "CLI verification did not report [OK]:\n" + output);
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

// eq reads the qubit count itself. It must accept OpenQASM 3 "qubit[N] name;",
// not only OpenQASM 2 "qreg name[N];" (#46).
BOOST_AUTO_TEST_CASE(eq_accepts_openqasm3_qubit_declaration)
{
    std::string dir = test_dir_from_file(__FILE__, "testcase/Qasm3Eq/");
    auto f = [&](const std::string& name) { return "\"" + dir + name + "\""; };
    const std::vector<std::pair<std::string, std::string>> cases = {
        {"eq " + f("h3.qasm") + " " + f("h2.qasm"), "[equal]"},
        {"eq " + f("h2.qasm") + " " + f("h3.qasm"), "[equal]"},
        {"eq " + f("h2.qasm") + " " + f("h2.qasm"), "[equal]"},
        {"eq " + f("h3.qasm") + " " + f("h3.qasm"), "[equal]"},
        {"eq " + f("x2.qasm") + " " + f("x3.qasm"), "[equal]"},
        {"eq " + f("h3.qasm") + " " + f("x3.qasm"), "[unequal]"},
        {"eq " + f("h2.qasm") + " " + f("x2.qasm"), "[unequal]"},
        {"eq " + f("x3.qasm") + " " + f("h2.qasm"), "[unequal]"},
    };
    for (const auto& [args, expected] : cases) {
        auto [code, output] = run_cli(args);
        BOOST_CHECK_MESSAGE(code == 0, args + ": exit status " + std::to_string(code) + ", output: " + output);
        BOOST_CHECK_MESSAGE(output.find(expected) != std::string::npos,
            args + ": expected \"" + expected + "\" in output: " + output);
    }
}

// A binary constant in x≠c must have exactly |x| bits. A shorter one used to
// abort in std::string::at, and a longer one was silently truncated (#35).
BOOST_AUTO_TEST_CASE(inequality_constant_must_match_variable_length)
{
    std::string dir = test_dir_from_file(__FILE__, "testcase/IneqLength/");
    auto f = [&](const std::string& name) { return "\"" + dir + name + "\""; };
    const std::vector<std::pair<std::string, std::string>> rejected = {
        {"print " + f("bad.hsl"), "x≠0\" must have length 2"},
        {"print " + f("bad_local.hsl"), "i≠0\" must have length 2"},
        {"print " + f("bad_order.hsl"), "x≠0\" must have length 2"},
        {"print " + f("bad_wide.hsl"), "x≠01\" must have length 3"},
        {"print " + f("long.hsl"), "x≠110\" must have length 2"},
    };
    for (const auto& [args, expected] : rejected) {
        auto [code, output] = run_cli(args);
        BOOST_CHECK_MESSAGE(code == 1, args + ": exit status " + std::to_string(code) + ", output: " + output);
        BOOST_CHECK_MESSAGE(output.find(expected) != std::string::npos,
            args + ": expected \"" + expected + "\" in output: " + output);
        BOOST_CHECK_MESSAGE(output.find("out_of_range") == std::string::npos,
            args + ": aborted instead of reporting a parse error: " + output);
    }
    const std::vector<std::pair<std::string, std::vector<std::string>>> accepted = {
        {"print " + f("good.hsl"), {"|01>", "|10>", "|11>"}},
        {"print " + f("good_local.hsl"), {"|01>", "|10>", "|11>"}},
        {"print " + f("good2.hsl"), {"|00>", "|01>", "|10>"}},
    };
    for (const auto& [args, needles] : accepted) {
        auto [code, output] = run_cli(args);
        BOOST_CHECK_MESSAGE(code == 0, args + ": exit status " + std::to_string(code) + ", output: " + output);
        for (const auto& needle : needles)
            BOOST_CHECK_MESSAGE(output.find(needle) != std::string::npos,
                args + ": expected \"" + needle + "\" in output: " + output);
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

// A qubit operand must be name[n] with n inside the declared register.
// A bare name, a missing operand, or an index past the register used to be
// executed as some other qubit, or to crash (#24).
BOOST_AUTO_TEST_CASE(qasm_qubit_index_must_be_in_range)
{
    std::string dir = test_dir_from_file(__FILE__, "testcase/QubitIndex/");
    auto f = [&](const std::string& name) { return "\"" + dir + name + "\""; };
    const std::vector<std::pair<std::string, std::string>> rejected = {
        {"ex " + f("two.hsl") + " " + f("x_oob.qasm"), "x qb[2]"},
        {"ex " + f("one.hsl") + " " + f("h_oob.qasm"), "h qb[1]"},
        {"ex " + f("one.hsl") + " " + f("h_bare.qasm"), "Expected 1 qubit operand"},
        {"ex " + f("one.hsl") + " " + f("x_bare.qasm"), "Expected 1 qubit operand"},
        {"ex " + f("one.hsl") + " " + f("z_bare.qasm"), "Expected 1 qubit operand"},
        {"ex " + f("two.hsl") + " " + f("cx_one.qasm"), "Expected 2 qubit operand"},
        {"ex " + f("two.hsl") + " " + f("cx_same.qasm"), "is repeated"},
        {"ex " + f("one.hsl") + " " + f("measure_oob.qasm"), "measure qb[1]"},
        {"ver " + f("one.hsl") + " " + f("measure_while.qasm") + " " + f("post_one.hsl"), "measure qb[1]"},
    };
    for (const auto& [args, expected] : rejected) {
        auto [code, output] = run_cli(args);
        BOOST_CHECK_MESSAGE(code == 1, args + ": exit status " + std::to_string(code) + ", output: " + output);
        BOOST_CHECK_MESSAGE(output.find(expected) != std::string::npos,
            args + ": expected \"" + expected + "\" in output: " + output);
        BOOST_CHECK_MESSAGE(output.find("[OK]") == std::string::npos, args + " reported [OK]: " + output);
    }

    auto [x0_code, x0_out] = run_cli("ex " + f("two.hsl") + " " + f("x0.qasm"));
    BOOST_CHECK_EQUAL(x0_code, 0);
    BOOST_CHECK_MESSAGE(x0_out.find("|10>") != std::string::npos, x0_out);

    auto [x1_code, x1_out] = run_cli("ex " + f("two.hsl") + " " + f("x1.qasm"));
    BOOST_CHECK_EQUAL(x1_code, 0);
    BOOST_CHECK_MESSAGE(x1_out.find("|01>") != std::string::npos, x1_out);

    auto [ry_code, ry_out] = run_cli("ex " + f("one.hsl") + " " + f("ry.qasm"));
    BOOST_CHECK_EQUAL(ry_code, 0);
    BOOST_CHECK_MESSAGE(ry_out.find("|0>") != std::string::npos, ry_out);
    BOOST_CHECK_MESSAGE(ry_out.find("|1>") != std::string::npos, ry_out);
}

// x≠y compares the two variables bit by bit, so |x| and |y| have to be the
// same length. The constraint list used to keep only one length, and the last
// |v|=N was applied to both variables.
BOOST_AUTO_TEST_CASE(variable_inequality_requires_equal_lengths)
{
    std::string dir = test_dir_from_file(__FILE__, "testcase/IneqVarLength/");
    auto print = [&](const std::string& name) { return run_cli("print \"" + dir + name + "\""); };

    auto [diff_code, diff_out] = print("diff.hsl");
    BOOST_CHECK_EQUAL(diff_code, 1);
    BOOST_CHECK_MESSAGE(diff_out.find("x≠y") != std::string::npos, diff_out);
    BOOST_CHECK_MESSAGE(diff_out.find("|x|=2") != std::string::npos, diff_out);
    BOOST_CHECK_MESSAGE(diff_out.find("|y|=3") != std::string::npos, diff_out);

    auto [order_code, order_out] = print("diff_order.hsl");
    BOOST_CHECK_EQUAL(order_code, 1);
    BOOST_CHECK_MESSAGE(order_out.find("|x|=2") != std::string::npos, order_out);
    BOOST_CHECK_MESSAGE(order_out.find("|y|=3") != std::string::npos, order_out);

    auto [local_code, local_out] = print("diff_local.hsl");
    BOOST_CHECK_EQUAL(local_code, 1);
    BOOST_CHECK_MESSAGE(local_out.find("i≠j") != std::string::npos, local_out);
    BOOST_CHECK_MESSAGE(local_out.find("|i|=2") != std::string::npos, local_out);
    BOOST_CHECK_MESSAGE(local_out.find("|j|=3") != std::string::npos, local_out);

    auto [missing_code, missing_out] = print("missing.hsl");
    BOOST_CHECK_EQUAL(missing_code, 1);
    BOOST_CHECK_MESSAGE(missing_out.find("must both have a declared length") != std::string::npos, missing_out);

    auto [same_code, same_out] = print("same.hsl");
    BOOST_CHECK_EQUAL(same_code, 0);
    BOOST_CHECK_MESSAGE(same_out.find("|0001>") != std::string::npos, same_out);
    BOOST_CHECK_MESSAGE(same_out.find("|0000>") == std::string::npos, same_out);
    BOOST_CHECK_MESSAGE(same_out.find("|1111>") == std::string::npos, same_out);

    auto [same_local_code, same_local_out] = print("same_local.hsl");
    BOOST_CHECK_EQUAL(same_local_code, 0);
    BOOST_CHECK_MESSAGE(same_local_out.find("|0001>") != std::string::npos, same_local_out);
    BOOST_CHECK_MESSAGE(same_local_out.find("|0000>") == std::string::npos, same_local_out);
}

// An .lsta label is [symbol,color]. A missing color used to abort in
// boost::bad_lexical_cast, and an internal label without a color was read as
// if the qubit index were the color (#36).
BOOST_AUTO_TEST_CASE(lsta_transition_requires_a_numeric_color)
{
    std::string dir = test_dir_from_file(__FILE__, "testcase/LstaColor/");
    using ConcreteParser = AUTOQ::Parsing::TimbukParser<Concrete>;
    using SymbolicParser = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>;
    using PredicateParser = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>;
    BOOST_CHECK_THROW(ConcreteParser::ReadAutomaton(dir + "uncolored_const.lsta"), AutoQError);
    BOOST_CHECK_THROW(ConcreteParser::ReadAutomaton(dir + "bad_leaf_color.lsta"), AutoQError);
    BOOST_CHECK_THROW(ConcreteParser::ReadAutomaton(dir + "bad_internal_color.lsta"), AutoQError);
    BOOST_CHECK_THROW(ConcreteParser::ReadAutomaton(dir + "uncolored_internal.lsta"), AutoQError);
    BOOST_CHECK_THROW(SymbolicParser::ReadAutomaton(dir + "uncolored_leaf.lsta"), AutoQError);
    BOOST_CHECK_THROW(PredicateParser::ReadAutomaton(dir + "uncolored_pred.lsta"), AutoQError);
    BOOST_CHECK_NO_THROW(SymbolicParser::ReadAutomaton(dir + "colored.lsta"));

    const std::vector<std::string> rejected = {
        "uncolored_leaf.lsta", "uncolored_const.lsta", "bad_leaf_color.lsta",
        "bad_internal_color.lsta", "uncolored_internal.lsta", "uncolored_pred.lsta",
    };
    for (const auto& name : rejected) {
        auto [code, output] = run_cli("print \"" + dir + name + "\"");
        BOOST_CHECK_MESSAGE(code == 1, name + ": exit status " + std::to_string(code) + ", output: " + output);
        BOOST_CHECK_MESSAGE(output.find("Invalid transition") != std::string::npos, output);
        BOOST_CHECK_MESSAGE(output.find("bad lexical cast") == std::string::npos, output);
    }

    auto [ok_code, ok_out] = run_cli("print \"" + dir + "colored.lsta\"");
    BOOST_CHECK_EQUAL(ok_code, 0);
    BOOST_CHECK_MESSAGE(ok_out.find("|0>") != std::string::npos, ok_out);
    BOOST_CHECK_MESSAGE(ok_out.find("|1>") != std::string::npos, ok_out);
}

// A Constraints or Constants line is parsed as one expression. Text after a
// valid prefix must not be dropped: "a = 1, b = 0" is not "a = 1". Separate
// lines, and "&&" on one line, are still one conjunction (#29).
BOOST_AUTO_TEST_CASE(constraint_line_must_be_fully_consumed)
{
    std::string dir = test_dir_from_file(__FILE__, "testcase/ConstraintTrailing/");
    auto f = [&](const std::string& name) { return "\"" + dir + name + "\""; };
    auto ver = [&](const std::string& post) {
        return run_cli("ver " + f("pre.hsl") + " " + f("circuit.qasm") + " " + f(post));
    };

    const std::vector<std::pair<std::string, std::string>> rejected = {
        {"post_comma.hsl", "unexpected trailing input at ','"},
        {"post_const.hsl", "unexpected trailing input at ')'"},
        {"post_const_tail.hsl", "unexpected trailing input at ')'"},
        {"post_amp.hsl", "token recognition error"},
    };
    for (const auto& [post, expected] : rejected) {
        auto [code, output] = ver(post);
        BOOST_CHECK_MESSAGE(code == 1, post + ": exit status " + std::to_string(code) + ", output: " + output);
        BOOST_CHECK_MESSAGE(output.find(expected) != std::string::npos,
            post + ": expected \"" + expected + "\" in output: " + output);
        BOOST_CHECK_MESSAGE(output.find("[OK]") == std::string::npos, post + " reported [OK]: " + output);
    }

    for (const char* post : {"post_and.hsl", "post_lines.hsl"}) {
        auto [code, output] = ver(post);
        BOOST_CHECK_MESSAGE(code == 0, std::string(post) + ": exit status " + std::to_string(code) + ", output: " + output);
        BOOST_CHECK_MESSAGE(output.find("[failed]") != std::string::npos, std::string(post) + ": " + output);
    }

    auto [ok_code, ok_out] = ver("post_const_ok.hsl");
    BOOST_CHECK_MESSAGE(ok_code == 0, ok_out);
    BOOST_CHECK_MESSAGE(ok_out.find("[OK]") != std::string::npos, ok_out);
}

// A leaf has no children, so [1,1] -> q is the amplitude 1, not qubit 1 (#30).
BOOST_AUTO_TEST_CASE(integer_leaf_is_an_amplitude)
{
    std::string dir = test_dir_from_file(__FILE__, "testcase/IntegerLeaf/");
    auto f = [&](const std::string& name) { return "\"" + dir + name + "\""; };
    auto aut = AUTOQ::Parsing::TimbukParser<Concrete>::ReadAutomaton(dir + "pre.lsta");
    BOOST_CHECK_EQUAL(aut.qubitNum, 1);
    int leaves = 0;
    int internals = 0;
    for (const auto& kv : aut.transitions) {
        if (kv.first.is_leaf()) ++leaves;
        if (kv.first.is_internal()) ++internals;
    }
    BOOST_CHECK_EQUAL(leaves, 2);
    BOOST_CHECK_EQUAL(internals, 1);
    auto amp2 = AUTOQ::Parsing::TimbukParser<Concrete>::ReadAutomaton(dir + "amp2.lsta");
    BOOST_CHECK_EQUAL(amp2.qubitNum, 1);

    auto [print_code, print_out] = run_cli("print " + f("pre.lsta"));
    BOOST_CHECK_EQUAL(print_code, 0);
    BOOST_CHECK_MESSAGE(print_out.find("(1/1)|0>") != std::string::npos, print_out);

    auto [x_code, x_out] = run_cli("ex " + f("pre.lsta") + " " + f("x.qasm"));
    BOOST_CHECK_EQUAL(x_code, 0);
    BOOST_CHECK_MESSAGE(x_out.find("(1/1)|1>") != std::string::npos, x_out);

    auto [h_code, h_out] = run_cli("ex " + f("pre.lsta") + " " + f("h.qasm"));
    BOOST_CHECK_EQUAL(h_code, 0);
    BOOST_CHECK_MESSAGE(h_out.find("|0>") != std::string::npos, h_out);
    BOOST_CHECK_MESSAGE(h_out.find("|1>") != std::string::npos, h_out);

    auto [ver_code, ver_out] = run_cli("ver " + f("pre.lsta") + " " + f("x.qasm") + " " + f("post.lsta"));
    BOOST_CHECK_MESSAGE(ver_code == 0, ver_out);
    BOOST_CHECK_MESSAGE(ver_out.find("[OK]") != std::string::npos, ver_out);

    auto [neg_code, neg_out] = run_cli("print " + f("neg.lsta"));
    BOOST_CHECK_EQUAL(neg_code, 0);
    BOOST_CHECK_MESSAGE(neg_out.find("|0>") != std::string::npos, neg_out);
    BOOST_CHECK_MESSAGE(neg_out.find("map::at") == std::string::npos, neg_out);
}

// .aut is not a supported input. It must get the same extension error as any
// other unknown suffix, not "The type of Complex is not supported!" (#48).
BOOST_AUTO_TEST_CASE(aut_extension_is_not_supported)
{
    std::string dir = test_dir_from_file(__FILE__, "testcase/AutExtension/");
    auto f = [&](const std::string& name) { return "\"" + dir + name + "\""; };
    const std::vector<std::string> commands = {
        "print " + f("zero.aut"),
        "print " + f("sym.aut"),
        "ex " + f("zero.aut") + " " + f("x.qasm"),
        "ver " + f("zero.hsl") + " " + f("x.qasm") + " " + f("zero.aut"),
    };
    for (const auto& command : commands) {
        auto [code, output] = run_cli(command);
        BOOST_CHECK_MESSAGE(code == 1, command + ": exit status " + std::to_string(code) + ", output: " + output);
        BOOST_CHECK_MESSAGE(output.find("The filename extension is not supported.") != std::string::npos, output);
        BOOST_CHECK_MESSAGE(output.find("The type of Complex is not supported!") == std::string::npos, output);
    }
}
