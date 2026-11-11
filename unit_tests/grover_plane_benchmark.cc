#include <chrono>
#include <exception>
#include <new>
#include "grover_span_util.hh"

namespace {
using namespace grover_span;
// Paper section 7.1: M=1; iterates 0,1,2 stay in span{alpha,beta}.
// Formula-derived obligations only, not execution of a quantum circuit.
void run(int n) {
    const C N=power2(n); C t(1),s(1);
    std::vector<V> iterates;
    for(int j=0;j<=2;++j) {
        iterates.push_back({t,s,C(0)});
        C nt=(N-C(2))*t-C(2)*s;
        s=C(2)*(N-C(1))*t+(N-C(2))*s; t=nt;
    }
    const auto b=amplitudes(n,n,{{C(1),C(0),C(0)},{C(0),C(1),C(0)}});
    expect("plane",n,amplitudes(n,n,iterates),b,Outcome::Included);
    expect("plane_leak",n,amplitudes(n,n,{{C(1),C(1),C(1)}}),b,Outcome::NotIncluded);
    if(n<=4) {
        const int dim=1<<n;
        std::vector<int> alpha(dim,1),beta(dim,0); alpha[0]=0; beta[0]=1;
        std::vector<std::vector<int>> rows{alpha,beta};
        for(int j=0;j<=2;++j) {
            auto v=dense_grover(n,n,j);
            require(C(v[1])==iterates[j][0],"dense unmarked amplitude mismatch");
            require(C(v[0])==iterates[j][1],"dense marked amplitude mismatch");
            rows.push_back(v);
        }
        require(span_test::rank(rows)==2U,"dense plane rank mismatch");
        std::vector<int> leak(dim,1); ++leak[dim/4]; rows.push_back(leak);
        require(span_test::rank(rows)==3U,"dense leakage rank mismatch");
        std::cout << "DENSE_ORACLE,passed" << std::endl;
    }
}
}
int main(int argc,char** argv) {
    if(argc==2 && (std::string(argv[1])=="--help" || std::string(argv[1])=="-h")) {
        std::cout << "Usage: grover_plane_benchmark --qubits N\n"
                     "N: integer in [2,65536]. Runs one size, positive and negative controls.\n"
                     "No built-in wall-clock or memory limit; no automatic sweep.\n"
                     "Formula-derived span inclusion, not circuit execution.\n";
        return 0;
    }
    int n=0;
    try {
        if(argc!=3 || std::string(argv[1])!="--qubits")
            throw std::invalid_argument("Usage: grover_plane_benchmark --qubits N");
        n=grover_span::parse_qubits(argv[2]);
    } catch(const std::exception& e) { std::cerr << e.what() << '\n'; return 4; }
    const auto began=std::chrono::steady_clock::now();
    int code=0; const char* status="passed";
    try { run(n); }
    catch(const std::bad_alloc& e) {
        std::cerr << "memory_failure: " << e.what() << '\n'; code=3; status="memory_failure";
    }
    catch(const std::exception& e) {
        std::cerr << "failed: " << e.what() << '\n'; code=1; status="failed";
    }
    const double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();
    std::cout << "SUMMARY,grover_paper_plane,qubits=" << n << ",status=" << status
              << ",seconds=" << seconds << std::endl;
    return code;
}
