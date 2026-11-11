#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>
#include <array>
#include <cstdlib>
#include <iostream>
#include <string>
#include "span_test_util.hh"

namespace {
using namespace AUTOQ::Span;
using C = AUTOQ::Complex::Complex;
using V = std::array<C,3>; // unmarked amplitude, marked amplitude, spike amplitude

std::vector<int> depths() {
    if (const char* p=std::getenv("AUTOQ_GROVER_QUBITS")) {
        const std::string text(p);
        std::size_t used=0;
        int n=std::stoi(text,&used);
        if (used!=text.size() || n<2 || n>65536)
            throw std::invalid_argument("Grover depth must be in [2,65536]");
        return {n};
    }
    return {2,3,4,8,16};
}
C power2(int n) {
    C v(1);
    for(int i=0;i<n;++i) v=v+v;
    return v;
}

// A depth-layered decision DAG. Marked strings have a zero prefix of length
// prefix. A distinct unmarked string 010...0 can receive a spike. Each root
// encodes one generator, not independent amplitude choices at each leaf.
Aut amplitudes(int n,int prefix,const std::vector<V>& generators) {
    Aut a; a.qubitNum=n; Aut::State next=0;
    for(const auto& v:generators) {
        const auto base=next;
        next+=4*(n+1);
        a.finalStates.push_back(base+3);
        for(int d=0;d<n;++d) for(int flags=0;flags<4;++flags) {
            Aut::StateVector children;
            for(int bit=0;bit<2;++bit) {
                bool marked=(flags&2) && (d>=prefix || bit==0);
                bool spike=(flags&1) && bit==(d==1 ? 1 : 0);
                children.push_back(base+4*(d+1)+(marked ? 2 : 0)+(spike ? 1 : 0));
            }
            span_test::edge(a,base+4*d+flags,d+1,1,children);
        }
        for(int flags=0;flags<4;++flags) {
            C value=(flags&2) ? v[1] : v[0];
            if(flags&1) value=value+v[2];
            a.transitions[Aut::SymbolTag(AUTOQ::Symbol::Concrete(value),1)]
                [base+4*n+flags].insert(Aut::StateVector{});
        }
    }
    a.stateNum=next;
    return a;
}

// Compact language of all computational basis vectors whose first two bits
// are 00 (M=N/4 solutions). Its language has 2^(n-2) runs and full solution
// rank, despite O(n) states. This intentionally exercises basis enumeration.
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
    span_test::leaf(a,2*n,1,3); span_test::leaf(a,2*n+1,0,3);
    return a;
}

Options options(int n) {
    Options o; o.qubits=n;
    o.limits.depth=0; o.limits.search_steps=0;
    return o; // benchmark harness supplies wall-clock and memory limits
}
void expect(const char* name,int n,const Aut& a,const Aut& b,Outcome wanted) {
    auto r=check_inclusion(a,b,options(n));
    std::cout << "GROVER," << name << ',' << n << ',' << to_string(r.outcome)
              << ",a_runs=" << r.stats.a_runs << ",b_runs=" << r.stats.b_runs
              << ",basis=" << r.stats.basis << ",tuples=" << r.stats.tuples
              << ",equations=" << r.stats.equations
              << ",search_steps=" << r.stats.search_steps << std::endl;
    BOOST_REQUIRE_MESSAGE(r.outcome==wanted,name << " n=" << n << " " << r.message);
    if(wanted==Outcome::NotIncluded) BOOST_REQUIRE(r.witness);
}

// Independent small dense oracle: apply phase oracle then N times diffusion
// directly to every coordinate. No production solver or pair recurrence.
std::vector<int> dense_grover(int n,int prefix,int iterations) {
    const int N=1<<n;
    std::vector<int> v(N,1);
    for(int j=0;j<iterations;++j) {
        for(int x=0;x<N;++x) if((x>>(n-prefix))==0) v[x]=-v[x];
        int sum=0; for(int x:v) sum+=x;
        for(auto& x:v) x=2*sum-N*x;
    }
    return v;
}
}

// Yan/Jiang/Yu, OOPSLA 2022, section 7.1, p.20: general Grover iterates stay
// in span{alpha,beta}. Choose one solution 0...0. Remove normalization and
// multiply each iterate by N to keep coefficients exact in FiveTuple.
// With amplitudes (t,s), the recurrence is
// t'=(N-2M)t-2Ms, s'=2(N-M)t+(N-2M)s. Here M=1.
// This is a paper-derived postcondition fixture, NOT circuit execution.
BOOST_AUTO_TEST_CASE(grover_paper_plane) {
    for(int n:depths()) {
        const C N=power2(n);
        C t(1),s(1);
        std::vector<V> iterates;
        for(int j=0;j<=2;++j) {
            iterates.push_back({t,s,C(0)});
            C nt=(N-C(2))*t-C(2)*s;
            s=C(2)*(N-C(1))*t+(N-C(2))*s;
            t=nt;
        }
        const auto b=amplitudes(n,n,{{C(1),C(0),C(0)},{C(0),C(1),C(0)}});
        expect("plane",n,amplitudes(n,n,iterates),b,Outcome::Included);
        // A spike distinguishes two unmarked amplitudes, hence leaves the plane.
        expect("plane_leak",n,amplitudes(n,n,{{C(1),C(1),C(1)}}),b,Outcome::NotIncluded);
        if(n<=4) {
            const int dim=1<<n;
            std::vector<int> alpha(dim,1), beta(dim,0); alpha[0]=0; beta[0]=1;
            std::vector<std::vector<int>> rows{alpha,beta};
            for(int j=0;j<=2;++j) {
                auto v=dense_grover(n,n,j);
                BOOST_CHECK(C(v[1])==iterates[j][0]);
                BOOST_CHECK(C(v[0])==iterates[j][1]);
                rows.push_back(v);
            }
            BOOST_CHECK_EQUAL(span_test::rank(rows),2U);
            std::vector<int> leak(dim,1); ++leak[dim/4]; rows.push_back(leak);
            BOOST_CHECK_EQUAL(span_test::rank(rows),3U);
        }
    }
}

// Figure 8 assumes parameters with success probability one. Instantiate
// M=N/4 (solutions 00*), R=1: theta=pi/3, so the iterate is entirely marked.
// Derive its unnormalized amplitudes via the recurrence, not by setting t=0.
// Check the premeasurement ray against the FULL solution subspace (not just
// uniform beta). Computational measurement preserves that subspace. Small n
// additionally checks the actual measured-support generators. The large-n
// benchmark measures the premeasurement inclusion and its negative control.
BOOST_AUTO_TEST_CASE(grover_paper_probability_one) {
    for(int n:depths()) {
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
}
