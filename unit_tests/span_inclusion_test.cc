#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE SpanInclusion
#include <boost/test/unit_test.hpp>
#include <random>
#include "autoq/span/inclusion.hh"
#include "span_test_util.hh"
using namespace AUTOQ::Span;
using C = AUTOQ::Complex::Complex;

// The equations 3*x=1 and 6*x=2 admit the non-dyadic solution x=1/3.
// Adding 3*x=2 must make the system inconsistent, even after a later 0=0 row.
BOOST_AUTO_TEST_CASE(non_dyadic_solution_and_persistent_contradiction) {
    detail::LinearSystem<C> s(1);
    BOOST_CHECK(s.add({C(3), C(1)}));
    BOOST_CHECK(s.add({C(6), C(2)}));
    BOOST_CHECK(!s.add({C(3), C(2)}));
    BOOST_CHECK(!s.add({C(0), C(0)}));
}
// Insert equations with pivots in reverse variable order, then a dependent row.
// Elimination must accept consistent rows and reject the final contradictory row.
BOOST_AUTO_TEST_CASE(out_of_order_pivots) {
    detail::LinearSystem<C> s(3);
    BOOST_CHECK(s.add({C(0), C(0), C(2), C(2)}));
    BOOST_CHECK(s.add({C(0), C(3), C(1), C(4)}));
    BOOST_CHECK(s.add({C(1), C(1), C(1), C(3)}));
    BOOST_CHECK(s.add({C(2), C(2), C(2), C(6)}));
    BOOST_CHECK(!s.add({C(2), C(2), C(2), C(7)}));
}
// Exact complex arithmetic must recognize i*x=1 and x=-i as compatible,
// reject x=i, and accept sqrt(2)*x=1 together with 2*x=sqrt(2).
BOOST_AUTO_TEST_CASE(complex_and_algebraic_coefficients) {
    const auto i = C::Angle(boost::rational<boost::multiprecision::cpp_int>(1,4));
    detail::LinearSystem<C> s(1);
    BOOST_CHECK(s.add({i, C(1)}));
    BOOST_CHECK(s.add({C(1), C(0)-i}));
    BOOST_CHECK(!s.add({C(1), i}));
    auto a = C::sqrt2();
    detail::LinearSystem<C> t(1);
    BOOST_CHECK(t.add({a, C(1)}));
    BOOST_CHECK(t.add({C(2), a}));
}
// A={(1,1)} is contained in the span of B={(1,0),(0,1),(2,0)}, but not its language.
// B has rank two; reverse inclusion fails and must return a witness from B.
BOOST_AUTO_TEST_CASE(span_is_not_language_inclusion_and_is_directional) {
    auto a = span_test::from_vectors(1, {{1,1}});
    auto b = span_test::from_vectors(1, {{1,0},{0,1},{2,0}});
    Options o; o.qubits=1;
    auto r = check_inclusion(a,b,o);
    BOOST_CHECK(r.outcome == Outcome::Included);
    BOOST_CHECK_EQUAL(r.stats.basis,2U);
    r = check_inclusion(b,a,o);
    BOOST_CHECK(r.outcome == Outcome::NotIncluded);
    BOOST_REQUIRE(r.witness);
    BOOST_CHECK_EQUAL(r.witness->root(), b.finalStates.front());
}
// Empty languages and zero vectors both span {0}; a nonzero vector does not.
// At depth zero, scalar 1 belongs to the span of scalar 3 without explicit division.
BOOST_AUTO_TEST_CASE(empty_and_zero_and_scalar_spaces) {
    Options o; o.qubits=1;
    auto e=span_test::from_vectors(1,{});
    auto z=span_test::from_vectors(1,{{0,0}});
    auto a=span_test::from_vectors(1,{{1,0}});
    BOOST_CHECK(check_inclusion(e,a,o).outcome==Outcome::Included);
    BOOST_CHECK(check_inclusion(z,e,o).outcome==Outcome::Included);
    BOOST_CHECK(check_inclusion(a,e,o).outcome==Outcome::NotIncluded);
    o.qubits=0;
    BOOST_CHECK(check_inclusion(span_test::from_vectors(0,{{1}}),
                                span_test::from_vectors(0,{{3}}),o).outcome==Outcome::Included);
}
// Leaf choice masks 3,6,5,7 intersect pairwise but have no common choice: no run exists.
// A repeated state must then share one transition at its level, and a saved run
// must remain usable for membership after the source transitions are cleared.
BOOST_AUTO_TEST_CASE(global_not_pairwise_choice_intersection) {
    Aut a; a.finalStates={0}; a.stateNum=7; a.qubitNum=2;
    span_test::edge(a,0,1,1,{1,2});
    span_test::edge(a,1,2,1,{3,4});
    span_test::edge(a,2,2,1,{5,6});
    span_test::leaf(a,3,1,3); span_test::leaf(a,4,1,6);
    span_test::leaf(a,5,1,5); span_test::leaf(a,6,1,7);
    Stats stats; std::size_t count=0;
    auto idx=detail::index_automaton(a);
    detail::enumerate(a,idx,2,Limits{},stats,count,[](const CompressedRun&){return true;});
    BOOST_CHECK_EQUAL(count,0U);
    a.transitions.clear();
    span_test::edge(a,0,1,1,{1,1});
    span_test::edge(a,1,2,2,{3,4});
    span_test::leaf(a,3,0,4); span_test::leaf(a,4,1,4);
    idx=detail::index_automaton(a); count=0; stats=Stats{};
    std::vector<CompressedRun> saved;
    detail::enumerate(a,idx,2,Limits{},stats,count,[&](const CompressedRun& r){saved.push_back(r);return true;});
    BOOST_REQUIRE_EQUAL(saved.size(),1U);
    BOOST_CHECK_EQUAL(saved[0].gamma[1].size(),1U);
    a.transitions.clear();
    Stats membership_stats;
    BOOST_CHECK(detail::member(saved[0],{saved[0]},Limits{},membership_stats));
}
// Different runs may select different transitions at the same root, yielding
// (1,0) and (0,1), whose span contains (1,1). Conversely, (1,2) is not a multiple
// of (1,1): membership must use one coefficient shared by every coordinate.
BOOST_AUTO_TEST_CASE(same_state_different_run_choices) {
    Aut b; b.finalStates={0}; b.stateNum=3; b.qubitNum=1;
    span_test::edge(b,0,1,1,{1,2});
    span_test::edge(b,0,1,2,{2,1});
    span_test::leaf(b,1,1,4); span_test::leaf(b,2,0,4);
    Options o; o.qubits=1;
    BOOST_CHECK(check_inclusion(span_test::from_vectors(1,{{1,1}}),b,o).outcome==Outcome::Included);
    BOOST_CHECK(check_inclusion(span_test::from_vectors(1,{{1,2}}),
                                span_test::from_vectors(1,{{1,1}}),o).outcome==Outcome::NotIncluded);
}
// A state with both a binary self-loop and a leaf transition is evaluated at
// fixed depth one, yielding (1,1) rather than requiring an acyclic automaton.
BOOST_AUTO_TEST_CASE(cycles_and_fixed_depth_filtering) {
    Aut a; a.finalStates={0}; a.stateNum=1; a.qubitNum=1;
    span_test::edge(a,0,1,1,{0,0}); span_test::leaf(a,0,1,2);
    Options o; o.qubits=1;
    BOOST_CHECK(check_inclusion(a,span_test::from_vectors(1,{{1,1}}),o).outcome==Outcome::Included);
}
// Although (1,1) is in the span of the two standard basis vectors, restricting
// basis size, search steps, tuples, or equations must report ResourceLimit,
// never turn an interrupted proof into a non-inclusion result.
BOOST_AUTO_TEST_CASE(limits_never_mean_non_inclusion) {
    auto a=span_test::from_vectors(1,{{1,1}});
    auto b=span_test::from_vectors(1,{{1,0},{0,1}});
    Options o; o.qubits=1; o.limits.basis=1;
    BOOST_CHECK(check_inclusion(a,b,o).outcome==Outcome::ResourceLimit);
    o.limits=Limits{}; o.limits.search_steps=1;
    BOOST_CHECK(check_inclusion(a,b,o).outcome==Outcome::ResourceLimit);
    o.limits=Limits{}; o.limits.tuples=1;
    BOOST_CHECK(check_inclusion(a,b,o).outcome==Outcome::ResourceLimit);
    o.limits=Limits{}; o.limits.equations=1;
    BOOST_CHECK(check_inclusion(a,b,o).outcome==Outcome::ResourceLimit);
}
// An 81-state chain with identical left/right children represents an all-ones
// vector with 2^80 coordinates. Self-inclusion must succeed using fewer than
// 1000 counted tuples, exercising compressed rather than dense traversal.
BOOST_AUTO_TEST_CASE(narrow_depth_80_no_dense_vectors) {
    Aut a; a.finalStates={0}; a.stateNum=81; a.qubitNum=80;
    for(int d=0;d<80;++d) span_test::edge(a,d,d+1,1,{d+1,d+1});
    span_test::leaf(a,80,1,1);
    Options o; o.qubits=80; o.limits.tuples=1000;
    auto r=check_inclusion(a,a,o);
    BOOST_CHECK(r.outcome==Outcome::Included);
    BOOST_CHECK(r.stats.tuples<1000U);
}
// Compare 80 reproducible cases at depths 0,1,2 against an independent exact
// dense-rank oracle: rank([B A]) == rank(B). Integer coordinates range from -2
// to 2; cases include empty B, dependent generators, and identical A/B inputs.
BOOST_AUTO_TEST_CASE(dense_oracle_fixed_seed) {
    std::mt19937 rng(77123);
    for(int trial=0;trial<80;++trial) {
        int n=trial%3, dimension=1<<n;
        std::vector<std::vector<int>> av,bv;
        for(int j=0;j<trial%5;++j) {
            std::vector<int> v(dimension);
            for(auto& x:v) x=static_cast<int>(rng()%5)-2;
            bv.push_back(v);
        }
        if(trial%2 && !bv.empty()) av=bv;
        else {
            std::vector<int> v(dimension);
            for(auto& x:v) x=static_cast<int>(rng()%5)-2;
            av.push_back(v);
        }
        auto both=bv; both.insert(both.end(),av.begin(),av.end());
        bool oracle=span_test::rank(both)==span_test::rank(bv);
        Options o; o.qubits=n;
        auto r=check_inclusion(span_test::from_vectors(n,av),span_test::from_vectors(n,bv),o);
        BOOST_REQUIRE(r.outcome==Outcome::Included || r.outcome==Outcome::NotIncluded);
        BOOST_CHECK_EQUAL(r.outcome==Outcome::Included,oracle);
    }
}

// Run Included, NotIncluded, and ResourceLimit checks on the same inputs.
// Their transitions, roots, state counts, and qubit counts must remain unchanged.
BOOST_AUTO_TEST_CASE(inputs_remain_unchanged_for_all_normal_outcomes) {
    auto a=span_test::from_vectors(1,{{1,1}});
    auto b=span_test::from_vectors(1,{{1,0},{0,1}});
    const auto at=a.transitions, bt=b.transitions;
    const auto ar=a.finalStates, br=b.finalStates;
    const auto an=a.stateNum, bn=b.stateNum;
    Options o; o.qubits=1;
    BOOST_CHECK(check_inclusion(a,b,o).outcome==Outcome::Included);
    BOOST_CHECK(check_inclusion(b,a,o).outcome==Outcome::NotIncluded);
    o.limits.basis=1;
    BOOST_CHECK(check_inclusion(a,b,o).outcome==Outcome::ResourceLimit);
    BOOST_CHECK(a.transitions==at); BOOST_CHECK(b.transitions==bt);
    BOOST_CHECK(a.finalStates==ar); BOOST_CHECK(b.finalStates==br);
    BOOST_CHECK_EQUAL(a.stateNum,an); BOOST_CHECK_EQUAL(b.stateNum,bn);
    BOOST_CHECK_EQUAL(a.qubitNum,1); BOOST_CHECK_EQUAL(b.qubitNum,1);
}
// Reject a unary internal transition and two same-parent transitions with
// overlapping choices as UnsupportedInput, without fabricating a witness.
BOOST_AUTO_TEST_CASE(malformed_arity_and_overlapping_choices_are_unsupported) {
    Options o; o.qubits=1;
    const auto good=span_test::from_vectors(1,{{1,0}});
    Aut malformed; malformed.finalStates={0}; malformed.stateNum=2;
    span_test::edge(malformed,0,1,1,{1});
    auto r=check_inclusion(good,malformed,o);
    BOOST_CHECK(r.outcome==Outcome::UnsupportedInput);
    BOOST_CHECK(!r.witness.has_value());
    auto overlap=good;
    span_test::edge(overlap,overlap.finalStates.front(),1,1,{2,1});
    r=check_inclusion(overlap,good,o);
    BOOST_CHECK(r.outcome==Outcome::UnsupportedInput);
    BOOST_CHECK(!r.witness.has_value());
}
// Three roots encode (1,0), (0,1), and (1,1). Returning false from the first
// callback must stop after one run; fresh enumeration must still visit all
// three, and the saved first run must remain valid for self-membership.
BOOST_AUTO_TEST_CASE(enumerator_cancellation_stops_without_visiting_other_roots) {
    const auto a=span_test::from_vectors(1,{{1,0},{0,1},{1,1}});
    const auto index=detail::index_automaton(a);
    Limits limits; Stats stats; std::size_t count=0;
    std::vector<CompressedRun> saved;
    detail::enumerate(a,index,1,limits,stats,count,[&](const CompressedRun& r) {
        saved.push_back(r); return false;
    });
    BOOST_CHECK_EQUAL(count,1U);
    BOOST_REQUIRE_EQUAL(saved.size(),1U);
    BOOST_CHECK_EQUAL(saved[0].root(),a.finalStates.front());
    stats=Stats{}; count=0;
    detail::enumerate(a,index,1,limits,stats,count,[](const CompressedRun&) {return true;});
    BOOST_CHECK_EQUAL(count,3U);
    Stats membership_stats;
    BOOST_CHECK(detail::member(saved[0],{saved[0]},limits,membership_stats));
}
// A per-automaton run limit of one permits complete singleton enumeration.
// A second B run exceeds that limit and must return ResourceLimit with one
// counted B run and no witness, rather than silently ignoring the extra run.
BOOST_AUTO_TEST_CASE(run_limit_distinguishes_exact_completion_from_truncation) {
    const auto a=span_test::from_vectors(1,{{1,0}});
    Options o; o.qubits=1; o.limits.runs=1;
    auto r=check_inclusion(a,a,o);
    BOOST_CHECK(r.outcome==Outcome::Included);
    BOOST_CHECK_EQUAL(r.stats.a_runs,1U); BOOST_CHECK_EQUAL(r.stats.b_runs,1U);
    const auto b=span_test::from_vectors(1,{{1,0},{0,1}});
    r=check_inclusion(a,b,o);
    BOOST_CHECK(r.outcome==Outcome::ResourceLimit);
    BOOST_CHECK_EQUAL(r.stats.b_runs,1U);
    BOOST_CHECK(!r.witness.has_value());
}
// A negative requested depth is UnsupportedInput; requesting depth two with
// a depth guard of one is ResourceLimit. Both checks must finish before search.
BOOST_AUTO_TEST_CASE(negative_depth_and_depth_guard_have_distinct_outcomes) {
    const auto a=span_test::from_vectors(1,{{1,0}});
    Options o; o.qubits=-1;
    auto r=check_inclusion(a,a,o);
    BOOST_CHECK(r.outcome==Outcome::UnsupportedInput);
    BOOST_CHECK_EQUAL(r.stats.search_steps,0U);
    o.qubits=2; o.limits.depth=1;
    r=check_inclusion(a,a,o);
    BOOST_CHECK(r.outcome==Outcome::ResourceLimit);
    BOOST_CHECK_EQUAL(r.stats.search_steps,0U);
    BOOST_CHECK(!r.witness.has_value());
}
