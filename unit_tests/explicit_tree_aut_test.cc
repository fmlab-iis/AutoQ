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
#include <fstream>
#include <autoq/autoq.hh>
#include <autoq/inclusion.hh>
#include <autoq/util/util.hh>
#include <autoq/complex/complex.hh>
#include <autoq/symbol/concrete.hh>
#include <autoq/aut_description.hh>
#include <autoq/parsing/timbuk_parser.hh>
#include <autoq/serialization/timbuk_serializer.hh>

#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE AutType
#include <boost/test/unit_test.hpp>

using AUTOQ::Complex::Complex;
using AUTOQ::Symbol::Concrete;

int size = 7; // the number of qubits.

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

                if (i < loop-1) {
                    if (before.name == "Random")
                        BOOST_REQUIRE_MESSAGE(!AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
                }
                else {
                    BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
				}
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(Y_gate_twice_to_identity)
{
    int n = size;
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(n), AUTOQ::TreeAutomata::basis(n)}) {
        int loop = 2;
        for (auto t : {1, n/2+1, n}) {
            AUTOQ::TreeAutomata after = before;
            for (int i=0; i<loop; i++) {
                after.Y(t);

                if (i < loop-1) {
                    BOOST_REQUIRE_MESSAGE(!AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
				}
                else {
                    BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
				}
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(Z_gate_twice_to_identity)
{
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(size), AUTOQ::TreeAutomata::basis(size)}) {
        AUTOQ::TreeAutomata after = before;
        int loop = 2;
        for (int i=0; i<loop; i++) {
            after.Z(size/2);

            if (i < loop-1) {
                BOOST_REQUIRE_MESSAGE(!AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
			}
            else {
                BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
			}
        }
    }
}

BOOST_AUTO_TEST_CASE(H_gate_twice_to_identity)
{
    int n = size;
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(n), AUTOQ::TreeAutomata::basis(n)}) {
        int loop = 2;
        for (auto t : {1, n/2+1, n}) {
            AUTOQ::TreeAutomata after = before;
            for (int i=0; i<loop; i++) {
                after.H(t);

                if (i < loop-1) {
                    BOOST_REQUIRE_MESSAGE(!AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
                }
                else {
                    BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
                }
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(S_gate_fourth_to_identity)
{
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(size), AUTOQ::TreeAutomata::basis(size)}) {
        AUTOQ::TreeAutomata after = before;
        int loop = 4;
        for (int i=0; i<loop; i++) {
            after.S(size/2);

            if (i < loop-1) {
                BOOST_REQUIRE_MESSAGE(!AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
            } else {
                BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(Sdg_gate_equal_to_S_three_times)
{
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(size),
                                AUTOQ::TreeAutomata::basis(size),
                                AUTOQ::TreeAutomata::random(size),
                                AUTOQ::TreeAutomata::zero(size),
                                AUTOQ::TreeAutomata::basis_zero_one_zero(size),
                                AUTOQ::TreeAutomata::zero_zero_one_zero(size),
                                AUTOQ::TreeAutomata::zero_one_zero(size)}) {
        AUTOQ::TreeAutomata after1 = before, after2 = before;
        for (int i=0; i<3; i++) after1.S(size/2);
        after2.Sdg(size/2);
        BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(after1, after2), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after1) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after2));
    }
}

BOOST_AUTO_TEST_CASE(T_gate_eighth_to_identity)
{
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(size), AUTOQ::TreeAutomata::basis(size)}) {
        AUTOQ::TreeAutomata after = before;
        int loop = 8;
        for (int i=0; i<loop; i++) {
            after.T(size/2);

            if (i < loop-1) {
                BOOST_REQUIRE_MESSAGE(!AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
            } else {
                BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(Tdg_gate_equal_to_T_seven_times)
{
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(size),
                                AUTOQ::TreeAutomata::basis(size),
                                AUTOQ::TreeAutomata::random(size),
                                AUTOQ::TreeAutomata::zero(size),
                                AUTOQ::TreeAutomata::basis_zero_one_zero(size),
                                AUTOQ::TreeAutomata::zero_zero_one_zero(size),
                                AUTOQ::TreeAutomata::zero_one_zero(size)}) {
        AUTOQ::TreeAutomata after1 = before, after2 = before;
        for (int i=0; i<7; i++) after1.T(size/2);
        after2.Tdg(size/2);
        BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(after1, after2), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after1) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after2));
    }
}

BOOST_AUTO_TEST_CASE(swap_gate_simply_exchanges_basis)
{
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(size),
                                AUTOQ::TreeAutomata::basis(size),
                                // AUTOQ::TreeAutomata::random(size),
                                AUTOQ::TreeAutomata::zero(size),
                                AUTOQ::TreeAutomata::basis_zero_one_zero(size),
                                AUTOQ::TreeAutomata::zero_zero_one_zero(size),
                                AUTOQ::TreeAutomata::zero_one_zero(size)}) {
        AUTOQ::TreeAutomata after = before;
        after.swap(size*1/3, size*2/3);
        BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
    }
}

BOOST_AUTO_TEST_CASE(Rx_gate_eighth_to_identity)
{
    int n = size;
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(n), AUTOQ::TreeAutomata::basis(n)}) {
        int loop = 8;
        for (auto t : {1, n/2+1, n}) {
            AUTOQ::TreeAutomata after = before;
            for (int i=0; i<loop; i++) {
                after.Rx(boost::rational<boost::multiprecision::cpp_int>(1, 4), t);

                if (i < loop-1) {
                    BOOST_REQUIRE_MESSAGE(!AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
                }
                else {
                    BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
				}
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(Ry_gate_eighth_to_identity)
{
    int n = size;
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(n), AUTOQ::TreeAutomata::basis(n)}) {
        int loop = 8;
        for (auto t : {1, n/2+1, n}) {
            AUTOQ::TreeAutomata after = before;
            for (int i=0; i<loop; i++) {
                after.Ry(t);

                if (i < loop-1) {
                    BOOST_REQUIRE_MESSAGE(!AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
                }
                else {
                    BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
				}
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(Rz_gate_eighth_to_identity)
{
    int n = size;
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(n), AUTOQ::TreeAutomata::basis(n)}) {
        int loop = 8;
        for (auto t : {1, n/2+1, n}) {
            AUTOQ::TreeAutomata after = before;
            for (int i=0; i<loop; i++) {
                after.Rz(boost::rational<boost::multiprecision::cpp_int>(1, 4), t);

                if (i < loop-1) {
                    BOOST_REQUIRE_MESSAGE(!AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
                }
                else {
                    BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
				}
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(CNOT_gate_twice_to_identity)
{
    int n = size;
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(n),
                               AUTOQ::TreeAutomata::basis(n),
                               AUTOQ::TreeAutomata::random(n)}) {
        AUTOQ::TreeAutomata after = before;
        int loop = 2;
        for (int i=0; i<loop; i++) {
            after.CNOT(n*2/3, n/3);

            if (i < loop-1) {
                if (before.name == "Random")
                    BOOST_REQUIRE_MESSAGE(!AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
            } else {
                BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(CZ_gate_twice_to_identity)
{
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(size), AUTOQ::TreeAutomata::basis(size)}) {
        AUTOQ::TreeAutomata after = before;
        int loop = 2;
        for (int i=0; i<loop; i++) {
            after.CZ(size*2/3, size/3);

            if (i < loop-1) {
                BOOST_REQUIRE_MESSAGE(!AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
            } else {
                BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(Toffoli_gate_twice_to_identity)
{
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(3),
                               AUTOQ::TreeAutomata::basis(3),
                               AUTOQ::TreeAutomata::random(3)}) {
        int v[] = {1,2,3};
        do {
            AUTOQ::TreeAutomata after = before;
            int loop = 2;
            for (int i=0; i<loop; i++) {
                after.Toffoli(v[0], v[1], v[2]);

                if (i < loop-1) {
                    if (before.name == "Random")
                        BOOST_REQUIRE_MESSAGE(!AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
                } else {
                    BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(before, after), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
                }
            }
        } while (std::next_permutation(v, v+3));
    }
}

// BOOST_AUTO_TEST_CASE(Fredkin_gate_twice_to_identity)
// {
//     for (const auto &before : {AUTOQ::TreeAutomata::uniform(3),
//                                AUTOQ::TreeAutomata::basis(3),
//                                AUTOQ::TreeAutomata::random(3)}) {
//         int v[] = {1,2,3};
//         do {
//             AUTOQ::TreeAutomata after = before;
//             int loop = 2;
//             for (int i=0; i<loop; i++) {
//                 after.Fredkin(v[0], v[1], v[2]);

//                 if (i < loop-1) {
//                     if (before.name == "Random")
//                         BOOST_REQUIRE_MESSAGE(!AUTOQ::TreeAutomata::check_equal(before, after), "a");
//                 } else {
//                     BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(before, after), "b");
//                 }
//             }
//         } while (std::next_permutation(v, v+3));
//     }
// }

// BOOST_AUTO_TEST_CASE(Bernstein_Vazirani)
// {
//     int n = size;
//     auto aut = AUTOQ::TreeAutomata::zero(n+1);

//     for (int i=1; i<=n+1; i++) {
//         aut.H(i);
//     }
//     aut.Z(n+1);
//     for (int i=1; i<=n; i++) {
//         auto aut2 = aut;
//         aut2.CNOT(i, n+1);
//         aut = aut.Union(aut2);
//     }
//     for (int i=1; i<=n; i++) {
//         aut.H(i);
//     }

//     AUTOQ::TreeAutomata ans;
//     ans.name = "Bernstein-Vazirani";
//     ans.qubitNum = n+1;
//     assert(ans.qubitNum >= 2);
//     ans.finalStates.push_back(0);
//     for (unsigned level=1; level<ans.qubitNum; level++) { /* Note that < does not include ans.qubitNum! */
//         if (level >= 2)
//             ans.transitions[Concrete(level)][2*level - 3].insert({2*level - 1, 2*level - 1});
//         ans.transitions[Concrete(level)][2*level - 2].insert({2*level - 1, 2*level});
//         ans.transitions[Concrete(level)][2*level - 2].insert({2*level, 2*level - 1});
//     }
//     ans.stateNum = 2*(ans.qubitNum-1) + 1;
//     ans.transitions[Concrete(Complex::Zero())][ans.stateNum++].insert({{}});
//     ans.transitions[Concrete(Complex::One().divide_by_the_square_root_of_two())][ans.stateNum++].insert({{}});
//     ans.transitions[Concrete(Complex::One().divide_by_the_square_root_of_two() * (-1))][ans.stateNum++].insert({{}});
//     ans.transitions[Concrete(ans.qubitNum)][static_cast<AUTOQ::TreeAutomata::State>(2*(ans.qubitNum-1) - 1)].insert({ans.stateNum - 3, ans.stateNum - 3});
//     ans.transitions[Concrete(ans.qubitNum)][static_cast<AUTOQ::TreeAutomata::State>(2*(ans.qubitNum-1))].insert({ans.stateNum - 2, ans.stateNum - 1});

//     // std::ofstream fileRhs("reference_answers/Bernstein_Vazirani" + std::to_string(n) + ".aut");
// 	// fileRhs << AUTOQ::Serialization::TimbukSerializer::Serialize(ans);
// 	// fileRhs.close();

//     BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(aut, ans), "\n" +
//                         AUTOQ::Serialization::TimbukSerializer::Serialize(aut) +
//                         AUTOQ::Serialization::TimbukSerializer::Serialize(ans));
// }

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

// BOOST_AUTO_TEST_CASE(NOW)
// {
//     std::cout << AUTOQ::Util::Convert::ToString(std::numeric_limits<__int128_t>::max()) << "\n";
//     std::cout << AUTOQ::Util::Convert::ToString(std::numeric_limits<__int128_t>::min()) << "\n";
// }

// Ref: https://demonstrations.wolfram.com/QuantumCircuitImplementingGroversSearchAlgorithm
// Ref: https://quantumcomputing.stackexchange.com/questions/2177/how-can-i-implement-an-n-bit-toffoli-gate
BOOST_AUTO_TEST_CASE(Grover_Search)
{
    int n = 4;
    assert(n >= 2);
    auto aut = AUTOQ::TreeAutomata::basis_zero_one_zero(n);

    /********************************/
    for (int i=1; i<=n; i++) aut.X(i);
    for (int i=n+1; i<=2*n+1; i++) aut.H(i);
    /**************************************/

    for (int iter=1; iter <= M_PI / (4 * asin(1 / pow(2, n/2.0))); iter++) {
        /****************************************/
        for (int i=1; i<=n; i++) aut.CNOT(i, n+i);
        /* multi-controlled NOT gate */
        if (n >= 3) {
            aut.Toffoli(n+1, n+2, 2*n+2);
            for (int i=3; i<=n; i++)
                aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
            aut.CNOT(3*n, 2*n+1);
            for (int i=n; i>=3; i--)
                aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
            aut.Toffoli(n+1, n+2, 2*n+2);
        } else {
            assert(n == 2);
            aut.Toffoli(3, 4, 5);
        }
        /*****************************/
        for (int i=1; i<=n; i++) aut.CNOT(i, n+i);
        /****************************************/

        /************************************/
        for (int i=n+1; i<=2*n; i++) aut.H(i);
        for (int i=n+1; i<=2*n; i++) aut.X(i);
        /* multi-controlled Z gate */
        if (n >= 3) {
            aut.Toffoli(n+1, n+2, 2*n+2);
            for (int i=3; i<n; i++) // Note that < does not include n!
                aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
            aut.CZ(3*n-1, 2*n);
            for (int i=n-1; i>=3; i--)
                aut.Toffoli(n+i, 2*n+i-1, 2*n+i);
            aut.Toffoli(n+1, n+2, 2*n+2);
        // } else if (n == 3) {
        //     aut.H(2*n);
        //     aut.Toffoli(4, 5, 6);
        //     aut.H(2*n);
        } else {
            assert(n == 2);
            aut.CZ(3, 4);
        }
        /***************************/
        for (int i=n+1; i<=2*n; i++) aut.X(i);
        for (int i=n+1; i<=2*n; i++) aut.H(i);
        /************************************/
    }

    /********************************/
    for (int i=1; i<=n; i++) aut.X(i);
    /********************************/

    // std::ofstream fileRhs("reference_answers/Grover" + std::to_string(n) + ".aut");
    // aut.fraction_simplification();
	// fileRhs << AUTOQ::Serialization::TimbukSerializer::Serialize(aut);
	// fileRhs.close();

    // char cwd[PATH_MAX];
    // if (getcwd(cwd, sizeof(cwd)) != NULL) {
    //     printf("Current working dir: %s\n", cwd);
    // } else {
    //     perror("getcwd() error");
    // }

    std::ifstream t("../../reference_answers/Grover" + std::to_string(n) + ".aut");
    std::stringstream buffer;
    buffer << t.rdbuf();
    auto ans = AUTOQ::Parsing::TimbukParser<AUTOQ::TreeAutomata::Symbol>::ParseString(buffer.str());
    // int n = (aut.qubitNum + 1) / 3;
    // aut.print_aut();

    /******************************** Answer Validation *********************************/
    BOOST_REQUIRE_MESSAGE(AUTOQ::TreeAutomata::check_equal(aut, ans), "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(aut) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(ans));
    // std::map<AUTOQ::TreeAutomata::State, AUTOQ::TreeAutomata::StateVector> edge;
    // std::map<AUTOQ::TreeAutomata::State, AUTOQ::TreeAutomata::Symbol> leaf;
    // std::vector<AUTOQ::TreeAutomata::StateVector> first_layers;
    // for (const auto &t : aut.transitions) {
    //     for (const auto &in_out : t.second) {
    //         const auto &in = in_out.first;
    //         for (const auto &s : in_out.second) {
    //             if (in.empty()) { // is leaf transition
    //                 assert(t.first.size() == 5);
    //                 leaf[s] = t.first;
    //             }
    //             if (t.first.size() == 1 && t.first[0] == 1) {
    //                 first_layers.push_back(in);
    //             } else {
    //                 assert(edge[s].empty());
    //                 edge[s] = in;
    //             }
    //         }
    //     }
    // }
    // unsigned N = 1, two_2n = 1;
    // for (int j=0; j<n; j++)
    //     N <<= 1; // N := 2^n
    // if (n == 2) two_2n = 8; // 2^(2n-1)
    // else two_2n = N * N; // 2^(2n)
    // std::vector<bool> ans_found(N);
    // for (const auto &fl : first_layers) {
    //     std::vector<double> prob;
    //     dfs(edge, leaf, fl, prob);
    //     // std::cout << AUTOQ::Util::Convert::ToString(prob) << "\n";
    //     unsigned ans = UINT_MAX / 2;
    //     for (unsigned i=0; i<prob.size(); i++) {
    //         if (prob[i] > 0) { /* in fact check != (make the compiler not complain) */
    //             ans = i / two_2n;
    //             break;
    //         }
    //     }
    //     // printf("%u\n", ans);

    //     std::vector<double> nonzero;
    //     for (unsigned i=0; i<prob.size(); i++) {
    //         if (i / two_2n != ans) {
    //             BOOST_REQUIRE_MESSAGE(prob[i] <= 0, ""); /* in fact check = (make the compiler not complain) */
    //         } else {
    //             int two_n_minus_1 = 1;
    //             if (n >= 3) {
    //                 for (int j=0; j<n-1; j++)
    //                     two_n_minus_1 *= 2; // 2 ^ (n-1)
    //             }
    //             if (i % two_n_minus_1 == 0) {
    //                 nonzero.push_back(prob[i]);
    //             } else {
    //                 BOOST_REQUIRE_MESSAGE(prob[i] <= 0, ""); /* in fact check = (make the compiler not complain) */
    //             }
    //         }
    //     }
    //     for (unsigned i=0; i<nonzero.size(); i+=2) {
    //         BOOST_REQUIRE_MESSAGE(nonzero[i] >= nonzero[i+1] && nonzero[i] <= nonzero[i+1], ""); /* in fact check = (make the compiler not complain) */
    //         if (i == ans*2)
    //             BOOST_REQUIRE_MESSAGE(nonzero[ans*2] * 2 >= 0.9, "");
    //         else
    //             BOOST_REQUIRE_MESSAGE(nonzero[i] < nonzero[ans*2], "");
    //     }
    //     BOOST_REQUIRE_MESSAGE(!ans_found[ans], "");
    //     ans_found[ans] = true;
    // }
    // for (unsigned i=0; i<N; i++)
    //     BOOST_REQUIRE_MESSAGE(ans_found[i], "");
    /************************************************************************************/
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
            aut.Toffoli(1, 2, n+2);
            for (int i=3; i<=n; i++)
                aut.Toffoli(i, n+i-1, n+i);
            aut.CNOT(2*n, n+1);
            for (int i=n; i>=3; i--)
                aut.Toffoli(i, n+i-1, n+i);
            aut.Toffoli(1, 2, n+2);
        } else {
            assert(n == 2);
            aut.Toffoli(1, 2, 3);
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
            aut.Toffoli(1, 2, n+2);
            for (int i=3; i<n; i++) // Note that < does not include n!
                aut.Toffoli(i, n+i-1, n+i);
            aut.CZ(2*n-1, n);
            for (int i=n-1; i>=3; i--)
                aut.Toffoli(i, n+i-1, n+i);
            aut.Toffoli(1, 2, n+2);
        // } else if (n == 3) {
        //     aut.H(2*n);
        //     aut.Toffoli(4, 5, 6);
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

// #include <filesystem>
// namespace fs = std::filesystem;
// BOOST_AUTO_TEST_CASE(Symbolic_into_Predicates)
// {
//     std::string path = "../../benchmarks/Symbolic/";
//     for (const auto & entry : fs::directory_iterator(path)) {
//         if (entry.is_directory()) {
//             if (strstr(entry.path().c_str(), "BernsteinVazirani99") != nullptr) continue;
//             if (strstr(entry.path().c_str(), "BernsteinVazirani1000") != nullptr) continue;
//             if (strstr(entry.path().c_str(), "MOGrover08") != nullptr) continue;
//             if (strstr(entry.path().c_str(), "MOGrover09") != nullptr) continue;
//             if (strstr(entry.path().c_str(), "SOGrover16") != nullptr) continue;
//             if (strstr(entry.path().c_str(), "SOGrover18") != nullptr) continue;
//             if (strstr(entry.path().c_str(), "SOGrover20") != nullptr) continue;
//             if (strstr(entry.path().c_str(), "OEGrover20") != nullptr) continue;
//             if (strstr(entry.path().c_str(), "OEGrover30") != nullptr) continue;
//             if (strstr(entry.path().c_str(), "OEGrover50") != nullptr) continue;
//             if (strstr(entry.path().c_str(), "OEGrover75") != nullptr) continue;
//             if (strstr(entry.path().c_str(), "OEGrover100") != nullptr) continue;

//             std::string automaton;
//             std::string constraint; // The following template argument does not matter.
//             AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::findAndSplitSubstring(std::string(entry.path()) + std::string("/pre.spec"), automaton, constraint);

//             AUTOQ::SymbolicAutomata aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ParseString(automaton);
//             aut.execute((std::string(entry.path()) + std::string("/circuit.qasm")).c_str());
//             aut.fraction_simplification();

//             AUTOQ::PredicateAutomata spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>::FromFileToAutomata((std::string(entry.path()) + std::string("/post.spec")).c_str());

//             AUTOQ::Constraint C(constraint.c_str());

//             BOOST_REQUIRE_MESSAGE(AUTOQ::is_spec_satisfied(C, aut, spec), "\n" +
//                         std::string(entry.path().c_str()) + "\n" +
//                         AUTOQ::Serialization::TimbukSerializer::Serialize(aut) +
//                         AUTOQ::Serialization::TimbukSerializer::Serialize(spec));
//         }
//     }
// }

// BOOST_AUTO_TEST_CASE(Symbolic_into_Predicates_bug)
// {
//     std::string path = "../../benchmarks/Symbolic-bug/";
//     for (const auto & entry : fs::directory_iterator(path)) {
//         if (entry.is_directory()) {
//             std::string automaton;
//             std::string constraint; // The following template argument does not matter.
//             AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::findAndSplitSubstring(std::string(entry.path()) + std::string("/pre.spec"), automaton, constraint);

//             AUTOQ::SymbolicAutomata aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ParseString(automaton);
//             aut.execute((std::string(entry.path()) + std::string("/circuit.qasm")).c_str());
//             aut.fraction_simplification();

//             AUTOQ::PredicateAutomata spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>::FromFileToAutomata((std::string(entry.path()) + std::string("/post.spec")).c_str());

//             AUTOQ::Constraint C(constraint.c_str());

//             BOOST_REQUIRE_MESSAGE(!AUTOQ::is_spec_satisfied(C, aut, spec), "\n" +
//                         AUTOQ::Serialization::TimbukSerializer::Serialize(aut) +
//                         AUTOQ::Serialization::TimbukSerializer::Serialize(spec));
//         }
//     }
// }

// BOOST_AUTO_TEST_SUITE_END()
