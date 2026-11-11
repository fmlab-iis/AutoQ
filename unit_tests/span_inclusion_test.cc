#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE SpanInclusion
#include <boost/test/unit_test.hpp>

#include <boost/multiprecision/cpp_int.hpp>
#include <boost/rational.hpp>

#include "autoq/span/inclusion.hh"
#include "autoq/inclusion.hh"
#include "span_test_util.hh"

using AUTOQ::Complex::Complex;
using AUTOQ::Span::Outcome;

struct SpanFixture {
    SpanFixture() {
        if constexpr (std::is_same_v<Complex, AUTOQ::Complex::nTuple>) {
            AUTOQ::Complex::nTuple::N = 4;
        }
    }
};
BOOST_TEST_GLOBAL_FIXTURE(SpanFixture);

BOOST_AUTO_TEST_CASE(solver_handles_three_c_eq_one_without_division)
{
    AUTOQ::Span::detail::IncrementalSolver solver(1);
    BOOST_TEST(solver.add_equation({Complex(3)}, Complex(1)));
    BOOST_TEST(solver.add_equation({Complex(0)}, Complex(0)));
    BOOST_TEST(!solver.add_equation({Complex(0)}, Complex(1)));
}

BOOST_AUTO_TEST_CASE(solver_handles_dependent_and_complex_equations)
{
    AUTOQ::Span::detail::IncrementalSolver solver(1);
    auto i = Complex::Angle(boost::rational<boost::multiprecision::cpp_int>(1, 4));
    BOOST_TEST(solver.add_equation({i}, i));
    BOOST_TEST(solver.add_equation({Complex(2)}, Complex(2)));
}

BOOST_AUTO_TEST_CASE(global_choice_intersection_is_required)
{
    AUTOQ::ConcreteAutomata aut;
    aut.qubitNum = 1;
    aut.finalStates = {0};
    aut.stateNum = 3;

    aut.transitions[{1, 1}][0].insert({1, 2});
    aut.transitions[{AUTOQ::Symbol::Concrete(Complex(1)), 0b01}][1].insert({{}});
    aut.transitions[{AUTOQ::Symbol::Concrete(Complex(2)), 0b10}][1].insert({{}});
    aut.transitions[{AUTOQ::Symbol::Concrete(Complex(3)), 0b10}][2].insert({{}});
    aut.transitions[{AUTOQ::Symbol::Concrete(Complex(4)), 0b100}][2].insert({{}});

    std::size_t enumerated = 0;
    std::size_t callbacks = 0;
    const auto status = AUTOQ::Span::detail::enumerate_compressed_runs(
        aut,
        1,
        0,
        enumerated,
        [&](const AUTOQ::Span::CompressedRun &) {
            ++callbacks;
            return true;
        });

    BOOST_TEST(status == Outcome::Included);
    BOOST_TEST(callbacks == 1U);
}

BOOST_AUTO_TEST_CASE(span_inclusion_can_hold_when_language_inclusion_fails)
{
    const auto aut_a = span_test::automaton_from_vectors(1, {{1, 1}});
    const auto aut_b = span_test::automaton_from_vectors(1, {{1, 0}, {0, 1}});

    AUTOQ::Span::Options opts;
    opts.qubits = 1;
    const auto span = AUTOQ::Span::check_inclusion(aut_a, aut_b, opts);
    BOOST_TEST(span.outcome == Outcome::Included);

    BOOST_TEST(!(aut_a <<= aut_b));
}

BOOST_AUTO_TEST_CASE(span_inclusion_is_directional)
{
    const auto aut_a = span_test::automaton_from_vectors(1, {{1, 1}});
    const auto aut_b = span_test::automaton_from_vectors(1, {{1, 0}, {0, 1}});

    AUTOQ::Span::Options opts;
    opts.qubits = 1;
    const auto reverse = AUTOQ::Span::check_inclusion(aut_b, aut_a, opts);
    BOOST_TEST(reverse.outcome == Outcome::NotIncluded);
    BOOST_TEST(reverse.witness.has_value());
}

BOOST_AUTO_TEST_CASE(empty_basis_only_contains_zero_vector)
{
    const auto zero = span_test::automaton_from_vectors(1, {{0, 0}});
    const auto nonzero = span_test::automaton_from_vectors(1, {{1, 0}});
    AUTOQ::ConcreteAutomata empty_b;
    empty_b.qubitNum = 1;

    AUTOQ::Span::Options opts;
    opts.qubits = 1;

    BOOST_TEST(AUTOQ::Span::check_inclusion(zero, empty_b, opts).outcome == Outcome::Included);
    BOOST_TEST(AUTOQ::Span::check_inclusion(nonzero, empty_b, opts).outcome == Outcome::NotIncluded);
}

BOOST_AUTO_TEST_CASE(n_zero_is_supported)
{
    const auto aut_a = span_test::automaton_from_vectors(0, {{1}});
    const auto aut_b = span_test::automaton_from_vectors(0, {{1}, {2}});

    AUTOQ::Span::Options opts;
    opts.qubits = 0;
    BOOST_TEST(AUTOQ::Span::check_inclusion(aut_a, aut_b, opts).outcome == Outcome::Included);
}

BOOST_AUTO_TEST_CASE(resource_limits_report_resource_limit_outcome)
{
    const auto aut_a = span_test::automaton_from_vectors(1, {{1, 1}});
    const auto aut_b = span_test::automaton_from_vectors(1, {{1, 0}, {0, 1}});

    AUTOQ::Span::Options opts;
    opts.qubits = 1;
    opts.limits.max_basis_runs = 1;

    const auto result = AUTOQ::Span::check_inclusion(aut_a, aut_b, opts);
    BOOST_TEST(result.outcome == Outcome::ResourceLimit);
}

BOOST_AUTO_TEST_CASE(duplicate_generators_are_not_retained_twice)
{
    const auto aut_a = span_test::automaton_from_vectors(1, {{1, 1}});
    const auto aut_b = span_test::automaton_from_vectors(1, {{1, 0}, {1, 0}, {0, 1}});

    AUTOQ::Span::Options opts;
    opts.qubits = 1;

    const auto result = AUTOQ::Span::check_inclusion(aut_a, aut_b, opts);
    BOOST_TEST(result.outcome == Outcome::Included);
    BOOST_TEST(result.stats.basis_runs_retained == 2U);
}

BOOST_AUTO_TEST_CASE(matches_dense_rank_oracle_on_fixed_seed_small_cases)
{
    const int n = 2;
    const int dim = 1 << n;
    const auto all = span_test::fixed_seed_vectors(6, dim, 7U);
    std::vector<std::vector<int>> b = {all[0], all[1], all[2]};
    std::vector<std::vector<int>> a = {all[3], all[4]};

    const bool oracle = span_test::dense_rank_span_inclusion(a, b);

    const auto aut_a = span_test::automaton_from_vectors(n, a);
    const auto aut_b = span_test::automaton_from_vectors(n, b);

    AUTOQ::Span::Options opts;
    opts.qubits = n;
    const auto result = AUTOQ::Span::check_inclusion(aut_a, aut_b, opts);

    BOOST_TEST((result.outcome == Outcome::Included) == oracle);
}

BOOST_AUTO_TEST_CASE(cycles_are_bounded_by_fixed_depth)
{
    AUTOQ::ConcreteAutomata aut;
    aut.qubitNum = 2;
    aut.finalStates = {0};
    aut.stateNum = 2;
    aut.transitions[{1, 1}][0].insert({0, 0});
    aut.transitions[{2, 1}][0].insert({1, 1});
    aut.transitions[{AUTOQ::Symbol::Concrete(Complex(1)), 1}][1].insert({{}});

    AUTOQ::Span::Options opts;
    opts.qubits = 2;
    BOOST_TEST(AUTOQ::Span::check_inclusion(aut, aut, opts).outcome == Outcome::Included);
}

BOOST_AUTO_TEST_CASE(large_depth_narrow_run_stays_supported)
{
    const int n = 14;
    std::vector<int> v(static_cast<std::size_t>(1U << n), 0);
    v[0] = 1;
    const auto aut = span_test::automaton_from_vectors(n, {v});

    AUTOQ::Span::Options opts;
    opts.qubits = n;
    const auto result = AUTOQ::Span::check_inclusion(aut, aut, opts);
    BOOST_TEST(result.outcome == Outcome::Included);
}

BOOST_AUTO_TEST_CASE(non_concrete_variants_are_rejected)
{
    AUTOQ::SymbolicAutomata sym;
    AUTOQ::ConcreteAutomata con = span_test::automaton_from_vectors(1, {{1, 0}});

    AUTOQ::Span::Options opts;
    opts.qubits = 1;
    const auto result = AUTOQ::Span::check_inclusion(
        AUTOQ::Span::AutomatonVariant(sym),
        AUTOQ::Span::AutomatonVariant(con),
        opts);
    BOOST_TEST(result.outcome == Outcome::UnsupportedInput);
}
