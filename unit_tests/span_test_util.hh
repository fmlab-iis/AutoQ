#ifndef AUTOQ_SPAN_TEST_UTIL_HH
#define AUTOQ_SPAN_TEST_UTIL_HH
#include <boost/rational.hpp>
#include <boost/multiprecision/cpp_int.hpp>
#include <stdexcept>
#include <vector>
#include "autoq/span/inclusion.hh"
namespace span_test {
using Aut=AUTOQ::ConcreteAutomata;
using C=AUTOQ::Complex::Complex;
inline void edge(Aut& a, Aut::State q, int qubit, Aut::Tag mask, Aut::StateVector children) {
    a.transitions[Aut::SymbolTag(AUTOQ::Symbol::Concrete(qubit),mask)][q].insert(std::move(children));
}
inline void leaf(Aut& a, Aut::State q, int value, Aut::Tag mask) {
    a.transitions[Aut::SymbolTag(AUTOQ::Symbol::Concrete(C(value)),mask)][q].insert(Aut::StateVector{});
}
inline Aut from_vectors(int n,const std::vector<std::vector<int>>& vectors) {
    if(n<0 || n>8) throw std::invalid_argument("Dense test depth out of range");
    Aut a; a.qubitNum=n; Aut::State next=0;
    for(const auto& v:vectors) {
        if(v.size()!=(std::size_t(1)<<n)) throw std::invalid_argument("Dense test width");
        std::vector<Aut::State> layer{next++}; a.finalStates.push_back(layer[0]);
        for(int d=0;d<n;++d) {
            std::vector<Aut::State> following;
            for(auto q:layer) {
                auto l=next++,r=next++; edge(a,q,d+1,1,{l,r});
                following.push_back(l); following.push_back(r);
            }
            layer=std::move(following);
        }
        for(std::size_t i=0;i<v.size();++i) leaf(a,layer[i],v[i],1);
    }
    a.stateNum=next; return a;
}
// Independent dense Gaussian rank over Q, using exact rational division.
// The production solver does not use this arithmetic or implementation.
inline std::size_t rank(const std::vector<std::vector<int>>& vectors) {
    using Q=boost::rational<boost::multiprecision::cpp_int>;
    if(vectors.empty()) return 0;
    std::vector<std::vector<Q>> m;
    for(const auto& v:vectors) {
        std::vector<Q> row; for(int x:v) row.emplace_back(x);
        m.push_back(std::move(row));
    }
    std::size_t r=0;
    for(std::size_t c=0;c<m[0].size() && r<m.size();++c) {
        std::size_t p=r; while(p<m.size() && m[p][c]==Q(0)) ++p;
        if(p==m.size()) continue;
        std::swap(m[p],m[r]); Q pivot=m[r][c];
        for(auto& x:m[r]) x/=pivot;
        for(std::size_t i=0;i<m.size();++i) if(i!=r) {
            Q factor=m[i][c];
            for(std::size_t j=0;j<m[i].size();++j) m[i][j]-=factor*m[r][j];
        }
        ++r;
    }
    return r;
}
}
#endif
