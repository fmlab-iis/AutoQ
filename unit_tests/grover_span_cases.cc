#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>
#include <cstdlib>
#include "grover_span_util.hh"

namespace {
using namespace grover_span;
// O(n) states, but 2^(n-2) independent solution generators (all strings 00*).
Aut solution_basis(int n) {
    Aut a; a.qubitNum=n; a.stateNum=2*(n+1); a.finalStates={0};
    for(int d=0;d<n;++d) {
        auto live=2*d, dead=2*d+1, l=2*(d+1), z=l+1;
        span_test::edge(a,dead,d+1,3,{z,z});
        if(d<2) span_test::edge(a,live,d+1,3,{l,z});
        else {
            span_test::edge(a,live,d+1,1,{l,z});
            span_test::edge(a,live,d+1,2,{z,l});
        }
    }
    span_test::leaf(a,2*n,1,3); span_test::leaf(a,2*n+1,0,3); return a;
}
}

// Paper Figure 8: M=N/4, R=1. With sin(theta)=sqrt(M/N), theta=pi/6
// and one Grover iteration rotates by 2*theta=pi/3 to success probability 1.
// Formula-derived output, NOT circuit execution. Check against the FULL
// solution subspace, including a leakage negative control and small dense
// measured-support checks. Normal CI uses n=3; scaling sets the environment.
BOOST_AUTO_TEST_CASE(grover_paper_probability_one) {
    const char* p=std::getenv("AUTOQ_GROVER_QUBITS");
    const int n=p ? parse_qubits(p) : 3;
    const C N=power2(n), M=power2(n-2);
    const C t=N-C(2)*M-C(2)*M;
    const C s=C(2)*(N-M)+(N-C(2)*M);
    BOOST_REQUIRE(t.isZero()); BOOST_REQUIRE(!s.isZero());
    const auto b=solution_basis(n);
    expect("probability_one",n,amplitudes(n,2,{{t,s,C(0)}}),b,Outcome::Included);
    expect("probability_one_leak",n,amplitudes(n,2,{{t,s,C(1)}}),b,Outcome::NotIncluded);
    if(n<=4) {
        const int dim=1<<n, marked=dim/4;
        const auto v=dense_grover(n,2,1);
        std::vector<std::vector<int>> measured;
        for(int x=0;x<dim;++x) {
            BOOST_CHECK(C(v[x])==(x<marked ? s : t));
            if(v[x]!=0) {
                std::vector<int> basis(dim,0); basis[x]=v[x]; measured.push_back(basis);
            }
        }
        BOOST_CHECK_EQUAL(span_test::rank(measured),static_cast<std::size_t>(marked));
        expect("measured_support",n,span_test::from_vectors(n,measured),b,Outcome::Included);
    }
}
