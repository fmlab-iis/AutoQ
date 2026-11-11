#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE SpanInclusion
#include <boost/test/unit_test.hpp>
#include <random>
#include "autoq/span/inclusion.hh"
#include "span_test_util.hh"
using namespace AUTOQ::Span;
using C = AUTOQ::Complex::Complex;

BOOST_AUTO_TEST_CASE(non_dyadic_solution_and_persistent_contradiction) {
    detail::LinearSystem<C> s(1);
    BOOST_CHECK(s.add({C(3), C(1)}));
    BOOST_CHECK(s.add({C(6), C(2)}));
    BOOST_CHECK(!s.add({C(3), C(2)}));
    BOOST_CHECK(!s.add({C(0), C(0)}));
}
BOOST_AUTO_TEST_CASE(out_of_order_pivots) {
    detail::LinearSystem<C> s(3);
    BOOST_CHECK(s.add({C(0), C(0), C(2), C(2)}));
    BOOST_CHECK(s.add({C(0), C(3), C(1), C(4)}));
    BOOST_CHECK(s.add({C(1), C(1), C(1), C(3)}));
    BOOST_CHECK(s.add({C(2), C(2), C(2), C(6)}));
    BOOST_CHECK(!s.add({C(2), C(2), C(2), C(7)}));
}
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
BOOST_AUTO_TEST_CASE(cycles_and_fixed_depth_filtering) {
    Aut a; a.finalStates={0}; a.stateNum=1; a.qubitNum=1;
    span_test::edge(a,0,1,1,{0,0}); span_test::leaf(a,0,1,2);
    Options o; o.qubits=1;
    BOOST_CHECK(check_inclusion(a,span_test::from_vectors(1,{{1,1}}),o).outcome==Outcome::Included);
}
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
BOOST_AUTO_TEST_CASE(narrow_depth_80_no_dense_vectors) {
    Aut a; a.finalStates={0}; a.stateNum=81; a.qubitNum=80;
    for(int d=0;d<80;++d) span_test::edge(a,d,d+1,1,{d+1,d+1});
    span_test::leaf(a,80,1,1);
    Options o; o.qubits=80; o.limits.tuples=1000;
    auto r=check_inclusion(a,a,o);
    BOOST_CHECK(r.outcome==Outcome::Included);
    BOOST_CHECK(r.stats.tuples<1000U);
}
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
