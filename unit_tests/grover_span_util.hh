#ifndef AUTOQ_GROVER_SPAN_UTIL_HH
#define AUTOQ_GROVER_SPAN_UTIL_HH
#include <array>
#include <iostream>
#include <stdexcept>
#include <string>
#include "span_test_util.hh"

namespace grover_span {
using namespace AUTOQ::Span;
using Aut=span_test::Aut;
using C=AUTOQ::Complex::Complex;
using V=std::array<C,3>;
inline void require(bool value,const std::string& message) {
    if(!value) throw std::runtime_error(message);
}
inline int parse_qubits(const std::string& text) {
    if(text.empty() || text.find_first_not_of("0123456789")!=std::string::npos)
        throw std::invalid_argument("qubits must be an integer in [2,65536]");
    const auto n=std::stoul(text);
    if(n<2 || n>65536) throw std::invalid_argument("qubits must be in [2,65536]");
    return static_cast<int>(n);
}
inline C power2(int n) {
    C v(1); for(int i=0;i<n;++i) v=v+v; return v;
}
// Shared decision DAG: unmarked, marked, and optional single-string spike.
// Each root represents one generator with globally shared amplitudes.
inline Aut amplitudes(int n,int prefix,const std::vector<V>& generators) {
    Aut a; a.qubitNum=n; Aut::State next=0;
    for(const auto& v:generators) {
        const auto base=next; next+=4*(n+1); a.finalStates.push_back(base+3);
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
    a.stateNum=next; return a;
}
inline Options options(int n) {
    Options o; o.qubits=n; o.limits.depth=0; o.limits.search_steps=0; return o;
}
inline void expect(const char* name,int n,const Aut& a,const Aut& b,Outcome wanted) {
    auto r=check_inclusion(a,b,options(n));
    std::cout << "GROVER," << name << ',' << n << ',' << to_string(r.outcome)
              << ",a_runs=" << r.stats.a_runs << ",b_runs=" << r.stats.b_runs
              << ",basis=" << r.stats.basis << ",tuples=" << r.stats.tuples
              << ",equations=" << r.stats.equations
              << ",search_steps=" << r.stats.search_steps << std::endl;
    require(r.outcome==wanted,std::string(name)+" n="+std::to_string(n)+" "+r.message);
    if(wanted==Outcome::NotIncluded) require(bool(r.witness),"missing negative witness");
}
// Independent dense oracle, used only for n<=4. Integer-scaled diffusion.
inline std::vector<int> dense_grover(int n,int prefix,int iterations) {
    const int N=1<<n; std::vector<int> v(N,1);
    for(int j=0;j<iterations;++j) {
        for(int x=0;x<N;++x) if((x>>(n-prefix))==0) v[x]=-v[x];
        int sum=0; for(int x:v) sum+=x;
        for(auto& x:v) x=2*sum-N*x;
    }
    return v;
}
}
#endif
