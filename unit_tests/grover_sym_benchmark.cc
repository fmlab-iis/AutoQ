#include <algorithm>
#include <chrono>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <iterator>
#include <new>
#include <stdexcept>
#include <string>
#include "autoq/inclusion.hh"
#include "autoq/parsing/parser/timbuk_parser.hh"
#include "span_test_util.hh"

namespace {
namespace fs=std::filesystem;
using Clock=std::chrono::steady_clock;
using Aut=span_test::Aut;
void require(bool b,const std::string& s) { if(!b) throw std::runtime_error(s); }
int number(const std::string& s) {
    if(s.empty() || s.find_first_not_of("0123456789")!=std::string::npos)
        throw std::invalid_argument("expected decimal qubit count");
    auto v=std::stoul(s);
    if(v<3 || v>65536) throw std::invalid_argument("qubits must be in [3,65536]");
    return static_cast<int>(v);
}
std::string read(const fs::path& p) {
    std::ifstream f(p); require(bool(f),"cannot read "+p.string());
    return std::string(std::istreambuf_iterator<char>(f),std::istreambuf_iterator<char>());
}
std::string compact(std::string s) {
    s.erase(std::remove_if(s.begin(),s.end(),[](unsigned char c) {
        return c==' ' || c=='\t' || c=='\r' || c=='\n';
    }),s.end()); return s;
}
struct Temporary {
    fs::path dir;
    Temporary() {
        const auto tag=std::to_string(Clock::now().time_since_epoch().count());
        for(int i=0;i<100;++i) {
            auto p=fs::temp_directory_path()/("autoq-grover-"+tag+"-"+std::to_string(i));
            if(fs::create_directory(p)) { dir=p; return; }
        }
        throw std::runtime_error("cannot create temporary directory");
    }
    ~Temporary() { std::error_code ec; fs::remove_all(dir,ec); }
};
// Two concrete generators, O(n) states each, one run per root.
// Flag 2 tracks answer equality; flag 1 tracks the fixed auxiliary suffix.
Aut generators(const std::string& answer,const std::string& suffix) {
    const int n=static_cast<int>(answer.size()),total=n+static_cast<int>(suffix.size());
    Aut a; a.qubitNum=total; Aut::State next=0;
    for(int high=0;high<2;++high) {
        const auto base=next; next+=4*(total+1); a.finalStates.push_back(base+3);
        for(int d=0;d<total;++d) for(int flags=0;flags<4;++flags) {
            Aut::StateVector children;
            for(int bit=0;bit<2;++bit) {
                bool match=(flags&2)!=0,valid=(flags&1)!=0;
                if(d<n) match=match && bit==answer[d]-'0';
                else valid=valid && bit==suffix[d-n]-'0';
                children.push_back(base+4*(d+1)+(match?2:0)+(valid?1:0));
            }
            span_test::edge(a,base+4*d+flags,d+1,1,children);
        }
        for(int flags=0;flags<4;++flags) {
            int value=(flags&1) && (high ? bool(flags&2) : !bool(flags&2));
            span_test::leaf(a,base+4*total+flags,value,1);
        }
    }
    a.stateNum=next; return a;
}
double elapsed(Clock::time_point a,Clock::time_point b) {
    return std::chrono::duration<double>(b-a).count();
}
void row(const std::string& method,int n,Clock::time_point t0,Clock::time_point t1,
         Clock::time_point t2,Clock::time_point t3,const std::string& outcome) {
    std::cout << std::setprecision(12) << "GROVER_COMPARE,method=" << method
              << ",search_qubits=" << n << ",total_qubits=" << 2*n-1
              << ",prepare_seconds=" << elapsed(t0,t1)
              << ",execute_seconds=" << elapsed(t1,t2)
              << ",check_seconds=" << elapsed(t2,t3)
              << ",total_seconds=" << elapsed(t0,t3) << ",outcome=" << outcome << std::endl;
}
}
int main(int argc,char** argv) {
    int n=0; std::string method="both"; fs::path root=".";
    try {
        for(int i=1;i<argc;++i) {
            const std::string key=argv[i];
            if(key=="--help" || key=="-h") {
                std::cout << "Usage: grover_sym_benchmark --qubits N [--method set|span|both|original] [--repo-root PATH]\n"
                             "N is SEARCH qubits (3..65536); total circuit qubits=2*N-1.\n"
                             "Uses existing benchmarks/all/GroverSym/NN files; does not generate circuits.\n"
                             "set/span check the complex plane without coefficient constraints.\n"
                             "original checks the stronger original symbolic postcondition.\n"
                             "Default: both, one run per method, repo root=current directory.\n"
                             "No --repeat option; no built-in time/memory limit.\n";
                return 0;
            }
            if(i+1>=argc) throw std::invalid_argument("missing option value");
            const std::string value=argv[++i];
            if(key=="--qubits") n=number(value);
            else if(key=="--method") method=value;
            else if(key=="--repo-root") root=value;
            else throw std::invalid_argument("unknown option: "+key);
        }
        if(n==0) throw std::invalid_argument("--qubits is required");
        if(method!="set" && method!="span" && method!="both" && method!="original")
            throw std::invalid_argument("invalid --method");
    } catch(const std::exception& e) { std::cerr << e.what() << '\n'; return 4; }
    try {
        const std::string size=(n<10 ? "0" : "")+std::to_string(n);
        const fs::path folder=root/"benchmarks"/"all"/"GroverSym"/size;
        std::string answer; for(int i=0;i<n;++i) answer+=i%2 ? '1' : '0';
        const std::string suffix=std::string(n-2,'0')+"1";
        const std::string expression="{pH |"+answer+suffix+"> + pL ∑ |i|="+
            std::to_string(n)+", i≠"+answer+" |i"+suffix+">}";
        const std::string post=read(folder/"post.hsl");
        require(compact(post.substr(0,post.find("Constraints")))==compact("Extended Dirac\n"+expression),
                "unsupported GroverSym post layout; refusing to guess answer/suffix");
        require(fs::is_regular_file(folder/"pre.hsl") && fs::is_regular_file(folder/"circuit.qasm"),
                "missing benchmark precondition or circuit");
        Temporary tmp; const auto plane=tmp.dir/"post.hsl";
        {
            std::ofstream f(plane); require(bool(f),"cannot write temporary post");
            f << "Extended Dirac\n" << expression << "\nConstraints\n"
                 "real(pH) = real(pH)\nimag(pH) = imag(pH)\n"
                 "real(pL) = real(pL)\nimag(pL) = imag(pL)\n";
            f.close(); require(bool(f),"failed writing temporary post");
        }
        std::cout << "GROVER_COMPARE_CONFIG,folder=" << folder.string() << ",method=" << method << std::endl;
        auto set_run=[&](bool original) {
            auto t0=Clock::now();
            auto parsed=AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadTwoAutomata(
                (folder/"pre.hsl").string(),(original ? folder/"post.hsl" : plane).string());
            auto a=parsed.first.at(0),b=parsed.first.at(1);
            auto t1=Clock::now(); a.execute((folder/"circuit.qasm").string(),parsed.second);
            auto t2=Clock::now(); const bool included=(a <<= b); auto t3=Clock::now();
            row(original?"original_set":"plane_set",n,t0,t1,t2,t3,included?"Included":"NotIncluded");
            return included;
        };
        auto span_run=[&]() {
            auto t0=Clock::now();
            auto parsed=AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadTwoAutomata(
                (folder/"pre.hsl").string(),(folder/"pre.hsl").string());
            auto a=parsed.first.at(0); auto b=generators(answer,suffix);
            AUTOQ::Span::Options options; options.qubits=2*n-1;
            options.limits.depth=0; options.limits.search_steps=0;
            auto t1=Clock::now(); a.execute((folder/"circuit.qasm").string(),parsed.second);
            auto t2=Clock::now(); auto r=AUTOQ::Span::check_inclusion(a,b,options); auto t3=Clock::now();
            row("plane_span",n,t0,t1,t2,t3,AUTOQ::Span::to_string(r.outcome));
            std::cout << "GROVER_COMPARE_STATS,a_runs=" << r.stats.a_runs << ",b_runs=" << r.stats.b_runs
                      << ",basis=" << r.stats.basis << ",tuples=" << r.stats.tuples
                      << ",equations=" << r.stats.equations << ",search_steps=" << r.stats.search_steps << std::endl;
            if(r.outcome!=AUTOQ::Span::Outcome::Included) std::cerr << r.message << '\n';
            return r.outcome==AUTOQ::Span::Outcome::Included && r.stats.basis==2;
        };
        bool ok=true;
        if(method=="set") ok=set_run(false);
        else if(method=="original") ok=set_run(true);
        else if(method=="span") ok=span_run();
        else { const bool s=set_run(false); const bool p=span_run(); ok=s && p; }
        return ok ? 0 : 1;
    } catch(const std::bad_alloc& e) { std::cerr << "memory_failure: " << e.what() << '\n'; return 3; }
    catch(const std::exception& e) { std::cerr << "error: " << e.what() << '\n'; return 1; }
}
