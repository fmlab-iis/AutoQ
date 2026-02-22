/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Copyright (c) 2011  Ondra Lengal <ilengal@fit.vutbr.cz>
 *
 *  Description:
 *    Test suite for explicit tree automaton
 *
 *****************************************************************************/

// AUTOQ headers
#include <cmath>
#include <filesystem>
#include <fstream>
#include <functional>

#include "autoq/error.hh"
#include "autoq/inclusion.hh"
#include "autoq/util/util.hh"
#include "autoq/complex/complex.hh"
#include "autoq/symbol/concrete.hh"
#include "autoq/aut_description.hh"
#include "autoq/parsing/parser/timbuk_parser.hh"
#include "autoq/serialization/timbuk_serializer.hh"
#include "test_util.hh"

#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE AutType
#include <boost/test/unit_test.hpp>

using AUTOQ::Complex::Complex;

/** Extended initial states for gate equivalence tests (Sdg/Tdg/swap). */
static std::vector<AUTOQ::TreeAutomata> kExtendedInitialStates(int n) {
    return {AUTOQ::TreeAutomata::uniform(n), AUTOQ::TreeAutomata::basis(n), AUTOQ::TreeAutomata::random(n),
            AUTOQ::TreeAutomata::zero(n), AUTOQ::TreeAutomata::basis_zero_one_zero(n),
            AUTOQ::TreeAutomata::zero_zero_one_zero(n), AUTOQ::TreeAutomata::zero_one_zero(n)};
}

/** Test gate applied loop times returns to identity. Positions empty = {1, n/2+1, n}. */
static void test_gate_n_times_to_identity(
    std::function<void(AUTOQ::TreeAutomata&, int)> gate_fn,
    int n, int loop,
    bool include_random = true,
    std::vector<int> positions = {}) {
    if (positions.empty()) positions = {1, n/2+1, n};
    auto states = include_random
        ? std::vector{AUTOQ::TreeAutomata::uniform(n), AUTOQ::TreeAutomata::basis(n), AUTOQ::TreeAutomata::random(n)}
        : std::vector{AUTOQ::TreeAutomata::uniform(n), AUTOQ::TreeAutomata::basis(n)};
    for (const auto& before : states) {
        for (int t : positions) {
            AUTOQ::TreeAutomata after = before;
            for (int i = 0; i < loop; i++) {
                gate_fn(after, t);
                if (i < loop - 1) {
                    BOOST_REQUIRE_MESSAGE(before != after, "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
                } else {
                    BOOST_REQUIRE_MESSAGE(before == after, "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
                }
            }
        }
    }
}

/** Test gate^gate_loop equals inverse_gate (e.g. S^3 == Sdg). */
static void test_gate_inverse_equivalence(
    std::function<void(AUTOQ::TreeAutomata&, int)> gate_fn,
    std::function<void(AUTOQ::TreeAutomata&, int)> inverse_fn,
    int n, int gate_loop, int qubit_pos) {
    for (const auto& before : kExtendedInitialStates(n)) {
        AUTOQ::TreeAutomata after1 = before, after2 = before;
        for (int i = 0; i < gate_loop; i++) gate_fn(after1, qubit_pos);
        inverse_fn(after2, qubit_pos);
        BOOST_REQUIRE_MESSAGE(after1 == after2, "\n" +
            AUTOQ::Serialization::TimbukSerializer::Serialize(after1) +
            AUTOQ::Serialization::TimbukSerializer::Serialize(after2));
    }
}

/** Run single-folder benchmark: ReadTwoAutomata, execute, check inclusion. */
static void run_single_folder_benchmark(const char* test_file, const std::string& rel_path,
                                        bool expect_inclusion, bool use_symbolic_symbolic = false) {
    std::string folder = test_dir_from_file(test_file, rel_path);
    if (use_symbolic_symbolic) {
        auto [autVec, qp] = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic, AUTOQ::Symbol::Symbolic>::ReadTwoAutomata(folder + "/pre.hsl", folder + "/post.hsl");
        auto aut2 = autVec.at(0);
        auto spec2 = autVec.at(1);
        aut2.execute(folder + "/circuit.qasm", qp);
        BOOST_REQUIRE_MESSAGE(expect_inclusion == (aut2 <<= spec2), folder + " failed!");
    } else {
        auto [autVec, qp] = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadTwoAutomata(folder + "/pre.hsl", folder + "/post.hsl");
        auto aut2 = autVec.at(0);
        auto spec2 = autVec.at(1);
        aut2.execute(folder + "/circuit.qasm", qp);
        BOOST_REQUIRE_MESSAGE(expect_inclusion == (aut2 <<= spec2), folder + " failed!");
    }
}

/** Shared benchmark verification: reads pre/post, executes circuit, checks inclusion. */
template<typename SymbolType>
void run_benchmark_verification(const char* test_file, const std::string& benchmark_rel_path, int max_size = kMaxBenchmarkSize) {
    std::string benchmarks = test_dir_from_file(test_file, benchmark_rel_path);
    for_each_benchmark_case(benchmarks, [](const std::string& folder) {
        auto [autVec, qp] = AUTOQ::Parsing::TimbukParser<SymbolType, SymbolType>::ReadTwoAutomata(folder + "/pre.hsl", folder + "/post.hsl");
        auto aut2 = autVec.at(0);
        auto spec2 = autVec.at(1);
        aut2.execute(folder + "/circuit.qasm", qp);
        BOOST_REQUIRE_MESSAGE(aut2 <<= spec2, folder + " failed!");
    }, max_size);
}
using AUTOQ::Symbol::Concrete;

int size = 14; // the number of qubits.

struct F {
    F() {
        BOOST_TEST_MESSAGE("Setup fixture.");
        if constexpr(std::is_same_v<AUTOQ::Complex::Complex, AUTOQ::Complex::nTuple>) {
            AUTOQ::Complex::nTuple::N = 4;
        }
    }
    ~F() { BOOST_TEST_MESSAGE("Teardown fixture."); }
};
BOOST_TEST_GLOBAL_FIXTURE(F);

BOOST_AUTO_TEST_CASE(X_gate_twice_to_identity)
{
    int n = size;
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(n),
                               AUTOQ::TreeAutomata::basis(n),
                               AUTOQ::TreeAutomata::random(n)}) {
        int loop = 2;
        for (auto t : {1, n/2+1, n}) {
            AUTOQ::TreeAutomata after = before;
            for (int i=0; i<loop; i++) {
                after.X(t);

                if (i < loop-1 && before.name == "Random") {
                    BOOST_REQUIRE_MESSAGE(before != after, "\n" +
                    AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                    AUTOQ::Serialization::TimbukSerializer::Serialize(after));
                } else {
                    BOOST_REQUIRE_MESSAGE(before == after, "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
				}
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(Y_gate_twice_to_identity)
{
    test_gate_n_times_to_identity([](AUTOQ::TreeAutomata& a, int t) { a.Y(t); }, size, 2);
}

BOOST_AUTO_TEST_CASE(Z_gate_twice_to_identity)
{
    test_gate_n_times_to_identity([](AUTOQ::TreeAutomata& a, int t) { a.Z(t); }, size, 2);
}

BOOST_AUTO_TEST_CASE(H_gate_twice_to_identity)
{
    test_gate_n_times_to_identity([](AUTOQ::TreeAutomata& a, int t) { a.H(t); }, size, 2);
}

BOOST_AUTO_TEST_CASE(S_gate_fourth_to_identity)
{
    test_gate_n_times_to_identity([](AUTOQ::TreeAutomata& a, int t) { a.S(t); }, size, 4);
}

BOOST_AUTO_TEST_CASE(Sdg_gate_equal_to_S_three_times)
{
    test_gate_inverse_equivalence([](auto& a, int t) { a.S(t); }, [](auto& a, int t) { a.Sdg(t); }, size, 3, size/2);
}

BOOST_AUTO_TEST_CASE(T_gate_eighth_to_identity)
{
    test_gate_n_times_to_identity([](AUTOQ::TreeAutomata& a, int t) { a.T(t); }, size, 8);
}

BOOST_AUTO_TEST_CASE(Tdg_gate_equal_to_T_seven_times)
{
    test_gate_inverse_equivalence([](auto& a, int t) { a.T(t); }, [](auto& a, int t) { a.Tdg(t); }, size, 7, size/2);
}

BOOST_AUTO_TEST_CASE(swap_gate_simply_exchanges_basis)
{
    for (const auto& before : std::vector{AUTOQ::TreeAutomata::uniform(size), AUTOQ::TreeAutomata::basis(size),
            AUTOQ::TreeAutomata::zero(size), AUTOQ::TreeAutomata::basis_zero_one_zero(size),
            AUTOQ::TreeAutomata::zero_zero_one_zero(size), AUTOQ::TreeAutomata::zero_one_zero(size)}) {
        AUTOQ::TreeAutomata after = before;
        after.Swap(size*1/3, size*2/3);
        BOOST_REQUIRE_MESSAGE(before == after, "\n" +
            AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
            AUTOQ::Serialization::TimbukSerializer::Serialize(after));
    }
}

BOOST_AUTO_TEST_CASE(Rx_gate_eighth_to_identity)
{
    test_gate_n_times_to_identity([](auto& a, int t) { a.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 4), t); }, size, 8, false);
}

BOOST_AUTO_TEST_CASE(Ry_gate_eighth_to_identity)
{
    test_gate_n_times_to_identity([](auto& a, int t) { a.Ry(t); }, size, 8, false);
}

BOOST_AUTO_TEST_CASE(Rz_gate_eighth_to_identity)
{
    test_gate_n_times_to_identity([](auto& a, int t) { a.Rz(boost::rational<boost::multiprecision::cpp_int>(1, 4), t); }, size, 8, false);
}

BOOST_AUTO_TEST_CASE(CX_gate_twice_to_identity)
{
    int n = size;
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(n),
                               AUTOQ::TreeAutomata::basis(n),
                               AUTOQ::TreeAutomata::random(n)}) {
        AUTOQ::TreeAutomata after = before;
        int loop = 2;
        for (int i=0; i<loop; i++) {
            after.CX(n*2/3, n/3);

            if (i < loop-1 && before.name == "Random") {
                BOOST_REQUIRE_MESSAGE(before != after, "\n" +
                    AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                    AUTOQ::Serialization::TimbukSerializer::Serialize(after));
            } else {
                BOOST_REQUIRE_MESSAGE(before == after, "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(CZ_gate_twice_to_identity)
{
    test_gate_n_times_to_identity([](auto& a, int) { a.CZ(size*2/3, size/3); }, size, 2, false, {0});
}

BOOST_AUTO_TEST_CASE(CCX_gate_twice_to_identity)
{
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(size*3/4+3),
                               AUTOQ::TreeAutomata::basis(size*3/4+3),
                               AUTOQ::TreeAutomata::random(size*3/4+3)}) {
        int v[] = {1, size*3/8, size*3/4};
        do {
            AUTOQ::TreeAutomata after = before;
            int loop = 2;
            for (int i=0; i<loop; i++) {
                after.CCX(v[0], v[1], v[2]);

                if (i < loop-1 && before.name == "Random") {
                    BOOST_REQUIRE_MESSAGE(before != after, "\n" +
                    AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                    AUTOQ::Serialization::TimbukSerializer::Serialize(after));
                } else {
                    BOOST_REQUIRE_MESSAGE(before == after, "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
                }
            }
        } while (std::next_permutation(v, v+3));
    }
}


BOOST_AUTO_TEST_CASE(for_loop_classic_execution){
    std::string folder = test_dir_from_file(__FILE__, "testcase/GroverFor/");
    auto [autVec, qp] = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadTwoAutomata(folder+"/pre.hsl", folder+"/post.hsl", folder+"/circuit.qasm");
    auto aut2 = autVec.at(0);
    auto spec2 = autVec.at(1);
    ParameterMap params;
    params["loop"] = "manual";
    bool verify = aut2.execute(folder + "/circuit.qasm", qp, autVec, params);
    BOOST_REQUIRE_MESSAGE(verify, folder + " failed!");
}

BOOST_AUTO_TEST_CASE(for_loop_summarization){
    std::string folder = test_dir_from_file(__FILE__, "testcase/GroverFor/");
    auto [autVec, qp] = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadTwoAutomata(folder+"/pre.hsl", folder+"/post.hsl", folder+"/circuit.qasm");
    auto aut2 = autVec.at(0);
    auto spec2 = autVec.at(1);
    autVec.erase(autVec.begin(), autVec.begin() + 2); // remove the first two elements
    ParameterMap params;
    params["loop"] = "symbolic";
    bool verify = aut2.execute(folder + "/circuit.qasm", qp, autVec, params);
    verify &= (aut2 <<= spec2);
    BOOST_REQUIRE_MESSAGE(verify, folder + " failed!");
}


void dfs(const std::map<AUTOQ::TreeAutomata::State, AUTOQ::TreeAutomata::StateVector> &edge,
         const std::map<AUTOQ::TreeAutomata::State, AUTOQ::TreeAutomata::SymbolTag> &leaf,
         const AUTOQ::TreeAutomata::StateVector &layer,
         #if defined COMPLEX_Plain
         std::vector<float128> &prob) {
         #else
         std::vector<double> &prob) {
         #endif
    for (const AUTOQ::TreeAutomata::State &s : layer) {
        const auto &new_layer = edge.at(s);
        if (!new_layer.empty()) {
            dfs(edge, leaf, new_layer, prob);
        } else {
            const auto &symbol = leaf.at(s).symbol().complex;
            prob.push_back(symbol.abs2());
        }
    }
}

BOOST_AUTO_TEST_CASE(Grover_Search_only_one_oracle)
{
    int n = 4;
    assert(n >= 2);
    auto aut = AUTOQ::TreeAutomata::zero_one_zero(n);

    /***********************/
    unsigned ans = 0;
    for (int i=0; i<n; i++) {
        ans <<= 1;
        ans |= (i&1);
    }
    /***********************/

    /**********************************/
    for (int i=1; i<=n+1; i++) aut.H(i);
    /**********************************/

    for (int iter=1; iter <= M_PI / (4 * asin(1 / pow(2, n/2.0))); iter++) {
        /********************************/
        for (int i=1; i<=n; i++) {
            if ((ans & (1 << (i-1))) == 0)
                aut.X(n+1-i);
        }
        /* multi-controlled NOT gate */
        if (n >= 3) {
            aut.CCX(1, 2, n+2);
            for (int i=3; i<=n; i++)
                aut.CCX(i, n+i-1, n+i);
            aut.CX(2*n, n+1);
            for (int i=n; i>=3; i--)
                aut.CCX(i, n+i-1, n+i);
            aut.CCX(1, 2, n+2);
        } else {
            assert(n == 2);
            aut.CCX(1, 2, 3);
        }
        /********************************/
        for (int i=1; i<=n; i++) {
            if ((ans & (1 << (i-1))) == 0)
                aut.X(n+1-i);
        }
        /********************************/

        /********************************/
        for (int i=1; i<=n; i++) aut.H(i);
        for (int i=1; i<=n; i++) aut.X(i);
        /* multi-controlled Z gate */
        if (n >= 3) {
            aut.CCX(1, 2, n+2);
            for (int i=3; i<n; i++) // Note that < does not include n!
                aut.CCX(i, n+i-1, n+i);
            aut.CZ(2*n-1, n);
            for (int i=n-1; i>=3; i--)
                aut.CCX(i, n+i-1, n+i);
            aut.CCX(1, 2, n+2);
        // } else if (n == 3) {
        //     aut.H(2*n);
        //     aut.CCX(4, 5, 6);
        //     aut.H(2*n);
        } else {
            assert(n == 2);
            aut.CZ(1, 2);
        }
        /********************************/
        for (int i=1; i<=n; i++) aut.X(i);
        for (int i=1; i<=n; i++) aut.H(i);
        /********************************/
    }

    /******************************** Answer Validation *********************************/
    std::map<AUTOQ::TreeAutomata::State, AUTOQ::TreeAutomata::StateVector> edge;
    std::map<AUTOQ::TreeAutomata::State, AUTOQ::TreeAutomata::SymbolTag> leaf;
    std::vector<AUTOQ::TreeAutomata::StateVector> first_layers;
    for (const auto &t : aut.transitions) {
        const auto &symbol_tag = t.first;
        for (const auto &out_ins : t.second) {
            const auto &s = out_ins.first;
            for (const auto &in : out_ins.second) {
                if (in.empty()) { // is leaf transition
                    assert(symbol_tag.is_leaf());
                    leaf[s] = symbol_tag;
                }
                if (symbol_tag.is_internal() && symbol_tag.symbol().qubit() == 1) {
                    first_layers.push_back(in);
                } else {
                    assert(edge[s].empty());
                    edge[s] = in;
                }
            }
        }
    }
    unsigned N, two_n_minus_one = 1;
    if (n <= 2) N = 4;
    else {
        for (int j=0; j<n-1; j++)
            two_n_minus_one <<= 1; // N := 2^(n-1)
        N = two_n_minus_one * 2; // N := 2^n
    }
    BOOST_REQUIRE_MESSAGE(first_layers.size() == 1, "");
    std::vector<bool> ans_found(N);
    for (const auto &fl : first_layers) {
        std::vector<double> prob;
        dfs(edge, leaf, fl, prob);
        // std::cout << prob.size() << AUTOQ::Util::Convert::ToString(prob) << "\n";
        std::vector<double> nonzero;
        for (unsigned i=0; i<prob.size(); i++) {
            if (i % two_n_minus_one != 0) {
                BOOST_REQUIRE_MESSAGE(prob[i] <= 0, ""); /* in fact check = (make the compiler not complain) */
            } else {
                nonzero.push_back(prob[i]);
            }
        }
        for (unsigned i=0; i<nonzero.size(); i+=2) {
            BOOST_REQUIRE_MESSAGE(nonzero[i] >= nonzero[i+1] && nonzero[i] <= nonzero[i+1], ""); /* in fact check = (make the compiler not complain) */
            if (i == ans*2)
                BOOST_REQUIRE_MESSAGE(nonzero[ans*2] * 2 >= 0.9, "");
            else
                BOOST_REQUIRE_MESSAGE(nonzero[i] < nonzero[ans*2], "");
        }
        BOOST_REQUIRE_MESSAGE(!ans_found[ans], "");
        ans_found[ans] = true;
    }
    for (unsigned i=0; i<N; i++) {
        if (i == ans)
            BOOST_REQUIRE_MESSAGE(ans_found[i], "");
        else
            BOOST_REQUIRE_MESSAGE(!ans_found[i], "");
    }
    /************************************************************************************/
}

#include <autoq/inclusion.hh>
namespace fs = std::filesystem;

BOOST_AUTO_TEST_CASE(benchmarks_OEGrover)
{
    run_benchmark_verification<AUTOQ::Symbol::Symbolic>(__FILE__, "../benchmarks/all/OEGrover/");
}

BOOST_AUTO_TEST_CASE(benchmarks_BV)
{
    run_benchmark_verification<AUTOQ::Symbol::Concrete>(__FILE__, "../benchmarks/all/BV/");
}

BOOST_AUTO_TEST_CASE(benchmarks_MOBV_reorder)
{
    run_benchmark_verification<AUTOQ::Symbol::Concrete>(__FILE__, "../benchmarks/all/MOBV_reorder/");
}

BOOST_AUTO_TEST_CASE(benchmarks_GHZzero)
{
    run_benchmark_verification<AUTOQ::Symbol::Concrete>(__FILE__, "../benchmarks/all/GHZzero/");
}

BOOST_AUTO_TEST_CASE(benchmarks_GHZall)
{
    run_benchmark_verification<AUTOQ::Symbol::Concrete>(__FILE__, "../benchmarks/all/GHZall/");
}

BOOST_AUTO_TEST_CASE(benchmarks_H2)
{
    run_benchmark_verification<AUTOQ::Symbol::Concrete>(__FILE__, "../benchmarks/all/H2/");
}

BOOST_AUTO_TEST_CASE(benchmarks_HXH)
{
    run_benchmark_verification<AUTOQ::Symbol::Concrete>(__FILE__, "../benchmarks/all/HXH/");
}

BOOST_AUTO_TEST_CASE(benchmarks_MCToffoli)
{
    run_benchmark_verification<AUTOQ::Symbol::Concrete>(__FILE__, "../benchmarks/all/MCToffoli/");
}

BOOST_AUTO_TEST_CASE(benchmarks_Grover)
{
    run_benchmark_verification<AUTOQ::Symbol::Concrete>(__FILE__, "../benchmarks/all/Grover/");
}

BOOST_AUTO_TEST_CASE(benchmarks_MOGrover)
{
    run_benchmark_verification<AUTOQ::Symbol::Concrete>(__FILE__, "../benchmarks/all/MOGrover/");
}

BOOST_AUTO_TEST_CASE(benchmarks_GroverSym)
{
    run_benchmark_verification<AUTOQ::Symbol::Symbolic>(__FILE__, "../benchmarks/all/GroverSym/");
}

BOOST_AUTO_TEST_CASE(benchmarks_GroverWhile)
{
    std::string benchmarks = test_dir_from_file(__FILE__, "../benchmarks/all/GroverWhile/");
    for_each_benchmark_case(benchmarks, [](const std::string& folder) {
        auto [autVec, qp] = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadTwoAutomata(folder+"/pre.hsl", folder+"/post.hsl", folder + "/circuit.qasm");
        auto aut2 = autVec.at(0);
        auto spec2 = autVec.at(1);
        autVec.erase(autVec.begin(), autVec.begin() + 2);  // remove the first two elements
        aut2.execute(folder + "/circuit.qasm", qp, autVec);
        BOOST_REQUIRE_MESSAGE(aut2 <<= spec2, folder + " failed!");
    });
}

BOOST_AUTO_TEST_CASE(benchmarks_MOGroverSym)
{
    run_benchmark_verification<AUTOQ::Symbol::Symbolic>(__FILE__, "../benchmarks/all/MOGroverSym/");
}

BOOST_AUTO_TEST_CASE(benchmarks_H2Sym)
{
    run_single_folder_benchmark(__FILE__, "../benchmarks/all/H2Sym/", true);
}

BOOST_AUTO_TEST_CASE(benchmarks_H2BugSym)
{
    run_single_folder_benchmark(__FILE__, "../benchmarks/all/H2BugSym/", false);
}

BOOST_AUTO_TEST_CASE(benchmarks_BVBugSym)
{
    run_single_folder_benchmark(__FILE__, "../benchmarks/all/BVBugSym/", false, true);
}

BOOST_AUTO_TEST_CASE(benchmarks_RUS)
{
    std::string benchmarks = test_dir_from_file(__FILE__, "../benchmarks/all/RUS/");
    for_each_benchmark_case(benchmarks, [](const std::string& folder) {
        auto [autVec, qp] = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadTwoAutomata(folder+"/pre.hsl", folder+"/post" + ((folder.ends_with("10a") || folder.ends_with("10c")) ? "_corrected" : "") + ".hsl", folder + "/circuit.qasm");
        auto aut2 = autVec.at(0);
        auto spec2 = autVec.at(1);
        autVec.erase(autVec.begin(), autVec.begin() + 2); // remove the first two elements
        aut2.execute(folder + "/circuit.qasm", qp, autVec);
        BOOST_REQUIRE_MESSAGE(aut2 <<= spec2, folder + " failed!");
    }, 999999);  // RUS: no size limit
}

BOOST_AUTO_TEST_CASE(qubit_reordering)
{
    for (int z=2; z<=5; z++) {
        AUTOQ::TreeAutomata spec;
        spec.qubitNum = z;
        int pow_of_two = 1;
        AUTOQ::TreeAutomata::State state_counter = 0;
        for (int level=1; level<=z; level++) {
            for (int i=0; i<pow_of_two; i++) {
                spec.transitions[{level, 1}][state_counter].insert({state_counter*2+1, state_counter*2+2});
                state_counter++;
            }
            pow_of_two *= 2;
        }
        for (AUTOQ::TreeAutomata::State i=state_counter; i<=state_counter*2; i++) {
            spec.transitions[AUTOQ::TreeAutomata::SymbolTag(AUTOQ::Symbol::Concrete(Complex(i)), 1)][i].insert({{}});
        }
        spec.finalStates.push_back(0);
        spec.stateNum = state_counter*2 + 1;
        /************************/
        AUTOQ::TreeAutomata spec2;
        spec2.qubitNum = z;
        pow_of_two = 1;
        state_counter = 0;
        for (int level=1; level<=z; level++) {
            for (int i=0; i<pow_of_two; i++) {
                spec2.transitions[{level, 1}][state_counter].insert({state_counter*2+1, state_counter*2+2});
                state_counter++;
            }
            pow_of_two *= 2;
        }
        for (AUTOQ::TreeAutomata::State i=state_counter; i<=state_counter*2; i++) {
            if (i % 2) // odd
                spec2.transitions[AUTOQ::TreeAutomata::SymbolTag(AUTOQ::Symbol::Concrete(Complex(state_counter + (i-state_counter)/2)), 1)][i].insert({{}});
            else // even
                spec2.transitions[AUTOQ::TreeAutomata::SymbolTag(AUTOQ::Symbol::Concrete(Complex((state_counter*3+1)/2 + (i-state_counter-1)/2)), 1)][i].insert({{}});
        }
        spec2.finalStates.push_back(0);
        spec2.stateNum = state_counter*2 + 1;
        /*****************************/
        AUTOQ::TreeAutomata aut = spec;
        for (int j=1; j<=z-1; j++)
            aut.SwapDown(j);
        // aut.print_language();
        // spec2.print_language();
        BOOST_REQUIRE_MESSAGE(aut == spec2, __LINE__);
        /*****************************/
        aut = spec2;
        for (int j=z; j>=2; j--)
            aut.SwapUp(j);
        // aut.print_language();
        // spec.print_language();
        BOOST_REQUIRE_MESSAGE(aut == spec, __LINE__);
    }
    for (int z=2; z<=6; z+=2) {
        AUTOQ::TreeAutomata spec;
        spec.qubitNum = z;
        for (int level=1; level<=z; level++) {
            if (level >= 2)
                spec.transitions[{level, 0b11}][2*level - 3].insert({2*level - 1, 2*level - 1});
            if (level % 2)
                spec.transitions[{level, 0b01}][2*level - 2].insert({2*level - 1, 2*level});
            spec.transitions[{level, 0b10}][2*level - 2].insert({2*level, 2*level - 1});
        }
        spec.transitions[AUTOQ::TreeAutomata::SymbolTag(AUTOQ::Symbol::Concrete(Complex::One()), 1)][2*z].insert({{}});
        spec.transitions[AUTOQ::TreeAutomata::SymbolTag(AUTOQ::Symbol::Concrete(Complex::Zero()), 1)][2*z - 1].insert({{}});
        spec.finalStates.push_back(0);
        spec.stateNum = 2*z + 1;
        /************************/
        AUTOQ::TreeAutomata spec2;
        spec2.qubitNum = z;
        for (int level=1; level<=z; level++) {
            if (level >= 2)
                spec2.transitions[{level, 0b11}][2*level - 3].insert({2*level - 1, 2*level - 1});
            if ((level+1) % 2)
                spec2.transitions[{level, 0b01}][2*level - 2].insert({2*level - 1, 2*level});
            spec2.transitions[{level, 0b10}][2*level - 2].insert({2*level, 2*level - 1});
        }
        spec2.transitions[AUTOQ::TreeAutomata::SymbolTag(AUTOQ::Symbol::Concrete(Complex::One()), 1)][2*z].insert({{}});
        spec2.transitions[AUTOQ::TreeAutomata::SymbolTag(AUTOQ::Symbol::Concrete(Complex::Zero()), 1)][2*z - 1].insert({{}});
        spec2.finalStates.push_back(0);
        spec2.stateNum = 2*z + 1;
        /*****************************/
        AUTOQ::TreeAutomata aut = spec;
        for (int j=1; j<=z; j+=2)
            aut.SwapDown(j);
        // aut.print_language();
        // spec2.print_language();
        BOOST_REQUIRE_MESSAGE(aut == spec2, __LINE__);
        /*****************************/
        aut = spec2;
        for (int j=1; j<=z; j+=2)
            aut.SwapDown(j);
        // aut.print_language();
        // spec.print_language();
        BOOST_REQUIRE_MESSAGE(aut == spec, __LINE__);
    }
}

