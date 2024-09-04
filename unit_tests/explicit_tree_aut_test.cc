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
#include <filesystem>

#include "autoq/error.hh"
#include "autoq/inclusion.hh"
#include "autoq/util/util.hh"
#include "autoq/complex/complex.hh"
#include "autoq/symbol/concrete.hh"
#include "autoq/aut_description.hh"
#include "autoq/parsing/timbuk_parser.hh"
#include "autoq/serialization/timbuk_serializer.hh"

#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE AutType
#include <boost/test/unit_test.hpp>

using AUTOQ::Complex::Complex;
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
    int n = size;
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(n), AUTOQ::TreeAutomata::basis(n)}) {
        int loop = 2;
        for (auto t : {1, n/2+1, n}) {
            AUTOQ::TreeAutomata after = before;
            for (int i=0; i<loop; i++) {
                after.Y(t);

                if (i < loop-1) {
                    BOOST_REQUIRE_MESSAGE(before != after, "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
				}
                else {
                    BOOST_REQUIRE_MESSAGE(before == after, "\n" +
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
                BOOST_REQUIRE_MESSAGE(before != after, "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
			}
            else {
                BOOST_REQUIRE_MESSAGE(before == after, "\n" +
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
                    BOOST_REQUIRE_MESSAGE(before != after, "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
                }
                else {
                    BOOST_REQUIRE_MESSAGE(before == after, "\n" +
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
        BOOST_REQUIRE_MESSAGE(after1 == after2, "\n" +
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
        BOOST_REQUIRE_MESSAGE(after1 == after2, "\n" +
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
        after.Swap(size*1/3, size*2/3);
        BOOST_REQUIRE_MESSAGE(before == after, "\n" +
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
                    BOOST_REQUIRE_MESSAGE(before != after, "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
                }
                else {
                    BOOST_REQUIRE_MESSAGE(before == after, "\n" +
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
                    BOOST_REQUIRE_MESSAGE(before != after, "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
                }
                else {
                    BOOST_REQUIRE_MESSAGE(before == after, "\n" +
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
                    BOOST_REQUIRE_MESSAGE(before != after, "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
                }
                else {
                    BOOST_REQUIRE_MESSAGE(before == after, "\n" +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(before) +
                        AUTOQ::Serialization::TimbukSerializer::Serialize(after));
				}
            }
        }
    }
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
    for (const auto &before : {AUTOQ::TreeAutomata::uniform(size), AUTOQ::TreeAutomata::basis(size)}) {
        AUTOQ::TreeAutomata after = before;
        int loop = 2;
        for (int i=0; i<loop; i++) {
            after.CZ(size*2/3, size/3);

            if (i < loop-1) {
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
//                         BOOST_REQUIRE_MESSAGE(before != after, "a");
//                 } else {
//                     BOOST_REQUIRE_MESSAGE(before == after, "b");
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
//         aut2.CX(i, n+1);
//         aut = aut || aut2;
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
        for (int i=1; i<=n; i++) aut.CX(i, n+i);
        /* multi-controlled NOT gate */
        if (n >= 3) {
            aut.CCX(n+1, n+2, 2*n+2);
            for (int i=3; i<=n; i++)
                aut.CCX(n+i, 2*n+i-1, 2*n+i);
            aut.CX(3*n, 2*n+1);
            for (int i=n; i>=3; i--)
                aut.CCX(n+i, 2*n+i-1, 2*n+i);
            aut.CCX(n+1, n+2, 2*n+2);
        } else {
            assert(n == 2);
            aut.CCX(3, 4, 5);
        }
        /*****************************/
        for (int i=1; i<=n; i++) aut.CX(i, n+i);
        /****************************************/

        /************************************/
        for (int i=n+1; i<=2*n; i++) aut.H(i);
        for (int i=n+1; i<=2*n; i++) aut.X(i);
        /* multi-controlled Z gate */
        if (n >= 3) {
            aut.CCX(n+1, n+2, 2*n+2);
            for (int i=3; i<n; i++) // Note that < does not include n!
                aut.CCX(n+i, 2*n+i-1, 2*n+i);
            aut.CZ(3*n-1, 2*n);
            for (int i=n-1; i>=3; i--)
                aut.CCX(n+i, 2*n+i-1, 2*n+i);
            aut.CCX(n+1, n+2, 2*n+2);
        // } else if (n == 3) {
        //     aut.H(2*n);
        //     aut.CCX(4, 5, 6);
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

    std::string sss(__FILE__);
    const auto &file = sss.substr(0, sss.find_last_of("\\/")) + "/reference_answers/Grover" + std::to_string(n) + ".spec";
    auto ans = AUTOQ::Parsing::TimbukParser<AUTOQ::TreeAutomata::Symbol>::ReadAutomaton(file);
    // int n = (aut.qubitNum + 1) / 3;
    // aut.print_aut();

    /******************************** Answer Validation *********************************/
    BOOST_REQUIRE_MESSAGE(aut == ans, "\n" +
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

//             AUTOQ::PredicateAutomata spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>::ReadAutomaton((std::string(entry.path()) + std::string("/post.spec")).c_str());

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

//             AUTOQ::PredicateAutomata spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>::ReadAutomaton((std::string(entry.path()) + std::string("/post.spec")).c_str());

//             AUTOQ::Constraint C(constraint.c_str());

//             BOOST_REQUIRE_MESSAGE(!AUTOQ::is_spec_satisfied(C, aut, spec), "\n" +
//                         AUTOQ::Serialization::TimbukSerializer::Serialize(aut) +
//                         AUTOQ::Serialization::TimbukSerializer::Serialize(spec));
//         }
//     }
// }

/*
bool is_symbol(std::string file)
{
    std::ifstream fin;
    fin.open(file);
    std::string word;
    while(fin>>word)
    {
        if(word == "Constraints")
            return 1;
    }
    return 0;
}

BOOST_AUTO_TEST_CASE(HSL_format_checker)
{

    for(int i = 0 ; i < 4 ; i++)
    {
        std::string hsl_file = "/home/johnny/AutoQ/unit_tests/testcase/spec_hsl/HSL/sample"+std::to_string(i)+".hsl";
        std::string spec_file = "/home/johnny/AutoQ/unit_tests/testcase/spec_hsl/SPEC/sample"+std::to_string(i)+".spec";
        std::cout<<hsl_file<<std::endl;
        std::cout<<spec_file<<std::endl;
        if(is_symbol(spec_file))
        {
            //auto aut_hsl  = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadAutomaton(hsl_file);
            //auto aut_spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadAutomaton(spec_file);
            //aut_spec.print_aut();
            //aut_hsl.print_aut();


            auto aut_hsl  = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadAutomaton(hsl_file);
            auto aut_spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>::ReadAutomaton(spec_file);
            std::string constraint = "";
            std::stringstream buffer;
            if (!constraint.empty()) {
                std::ifstream t(constraint);
                if (!t) // in case the file could not be open
                    THROW_AUTOQ_ERROR("Failed to open file " + std::string(constraint) + ".");
                buffer << t.rdbuf();
            }
            // AUTOQ::Constraint C(buffer.str().c_str());
            // bool verify_1 = AUTOQ::check_inclusion(C, aut_hsl, aut_spec);
            // BOOST_REQUIRE_MESSAGE(verify_1, "");


        }
        else
        {
            auto aut_hsl  = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(hsl_file);
            auto aut_spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(spec_file);
            bool res = (aut_hsl <= aut_spec) && (aut_spec <= aut_hsl);
            BOOST_REQUIRE_MESSAGE(res, "");
        }
    }
}

*/

/*
namespace fs = std::filesystem;

bool has_dir(const std::string &path)
{
    for (const auto & entry : fs::directory_iterator(path))
    {
        if(entry.is_directory())
            return 1;
    }
    return 0;
}

void search(std::string path, std::list<std::string> &not_found_list)
{
    for (const auto & entry : fs::directory_iterator(path))
    {
        if(!entry.is_directory())
        {
            continue;
        }
        if(has_dir(entry.path().string()))
        {
            search(entry.path().string(),not_found_list);
        }
        else
        {
            std::string pre_hsl = entry.path().string() + "/pre.hsl";
            std::string pre_spec = entry.path().string() + "/pre.spec";
            std::string post_hsl = entry.path().string() + "/post.hsl";
            std::string post_spec = entry.path().string() + "/post.spec";
            if(!fs::exists(pre_hsl))
                not_found_list.push_back(pre_hsl);
            if(!fs::exists(pre_spec))
                not_found_list.push_back(pre_spec);
            if(!fs::exists(post_hsl))
                not_found_list.push_back(pre_hsl);
            if(!fs::exists(post_spec))
                not_found_list.push_back(pre_hsl);
        }
    }

}

BOOST_AUTO_TEST_CASE(file_exist_checker)
{
    std::ofstream fout;
    fout.open("./file_exist_checker.csv");
    std::vector<std::list<std::string>> not_found_list;
    not_found_list.resize(3);
    not_found_list[0].push_back("./benchmarks/CAV23");
    not_found_list[1].push_back("./benchmarks/PLDI23");
    not_found_list[2].push_back("./benchmarks/POPL24");
    std::string path = "./benchmarks/CAV23/";
    for(int i = 0 ; i < 3 ; i++)
    {
        search(not_found_list[i].front(),not_found_list[i]);
    }
    int cnt[3];
    cnt[0] = 0, cnt[1] = 0, cnt[2] = 0;
    bool end_list[3];
    end_list[0] = 0, end_list[1] = 0, end_list[2] = 0;
    while(!end_list[0] || !end_list[1] || !end_list[2])
    {
        for(int i = 0 ; i < 3 ; i++)
        {
            std::string file = "";
            if(not_found_list[i].empty())
            {
                end_list[i] = 1;
            }
            else
            {
                file = not_found_list[i].front();
                not_found_list[i].pop_front();
            }
            fout<<file<<",";
        }
        fout<<std::endl;
    }
}
*/

#include <autoq/inclusion.hh>
namespace fs = std::filesystem;
BOOST_AUTO_TEST_CASE(hsl_rule_checker)
{
    std::string sss(__FILE__);
    //read ./unit_tests/hsl_rule/;
    std::string path = sss.substr(0, sss.find_last_of("\\/")) + "/testcase/";


    std::string cir_path = path + "GHZALL/circuit.qasm";
    std::string state_dir = path + "GHZALL/state/";
    for (const auto & entry : fs::directory_iterator(state_dir))
    {
        if(!entry.is_directory())
            continue;
        auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(entry.path().string() + "/pre.hsl");
        auto aut2 = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(entry.path().string() + "/post.hsl");
        aut.execute(cir_path);
        bool verify = aut <= aut2;
        BOOST_CHECK_MESSAGE(verify, entry.path().string() + " Not verified");
        // std::cout<<entry.path().string() + " Not verified"<<std::endl;
    }

    cir_path = path + "BVALL/circuit.qasm";
    state_dir = path + "BVALL/state/";
    for (const auto & entry : fs::directory_iterator(state_dir))
    {
        if(!entry.is_directory())
            continue;
        auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(entry.path().string() + "/pre.hsl");
        auto aut2 = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(entry.path().string() + "/post.hsl");
        aut.execute(cir_path);
        bool verify = aut <= aut2;
        BOOST_CHECK(verify);
        if(!verify)
            std::cout<<entry.path().string() + " Not verified"<<std::endl;
    }
    /*
    cir_path = path + "OEGROVER/circuit.qasm";
    state_dir = path + "OEGROVER/state/";
    for (const auto & entry : fs::directory_iterator(state_dir))
    {
        if(!entry.is_directory())
            continue;


        AUTOQ::SymbolicAutomata aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadAutomaton(entry.path().string() + "/pre.hsl");
        AUTOQ::PredicateAutomata aut2 = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>::ReadAutomaton(entry.path().string() + "/post.hsl");
        aut.execute(cir_path);
        bool verify = AUTOQ::check_inclusion(AUTOQ::Constraint(aut.constraints.c_str()), aut, aut2);
        BOOST_CHECK(verify);
        if(!verify)
            std::cout<<entry.path().string() + " Not verified"<<std::endl;
    }
    */
}

BOOST_AUTO_TEST_CASE(benchmarks_OEGrover)
{
    std::string sss(__FILE__);
    std::string benchmarks = sss.substr(0, sss.find_last_of("\\/")) + "/../benchmarks/_all/OEGrover/";
    for (const auto &entry : fs::directory_iterator(benchmarks)) {
        if (!entry.is_directory() || std::stoi(entry.path().string().substr(entry.path().string().find_last_of('/') + 1)) > 6) continue;
        auto folder = entry.path().string();
        auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadAutomaton(folder + "/pre.spec");
        auto spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>::ReadAutomaton(folder + "/post.spec");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(AUTOQ::check_inclusion(AUTOQ::Constraint(aut.constraints.c_str()), aut, spec), folder + " failed!");
        aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadAutomaton(folder + "/pre.hsl");
        spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>::ReadAutomaton(folder + "/post.hsl");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(AUTOQ::check_inclusion(AUTOQ::Constraint(aut.constraints.c_str()), aut, spec), folder + " failed!");
    }
}

BOOST_AUTO_TEST_CASE(benchmarks_BV)
{
    std::string sss(__FILE__);
    std::string benchmarks = sss.substr(0, sss.find_last_of("\\/")) + "/../benchmarks/_all/BV/";
    for (const auto &entry : fs::directory_iterator(benchmarks)) {
        if (!entry.is_directory() || std::stoi(entry.path().string().substr(entry.path().string().find_last_of('/') + 1)) > 6) continue;
        auto folder = entry.path().string();
        auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.spec");
        auto spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.spec");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
        aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.hsl");
        spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.hsl");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
    }
}

BOOST_AUTO_TEST_CASE(benchmarks_MOBV_reorder)
{
    std::string sss(__FILE__);
    std::string benchmarks = sss.substr(0, sss.find_last_of("\\/")) + "/../benchmarks/_all/MOBV_reorder/";
    for (const auto &entry : fs::directory_iterator(benchmarks)) {
        if (!entry.is_directory() || std::stoi(entry.path().string().substr(entry.path().string().find_last_of('/') + 1)) > 6) continue;
        auto folder = entry.path().string();
        auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.spec");
        auto spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.spec");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
        aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.hsl");
        spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.hsl");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
    }
}

BOOST_AUTO_TEST_CASE(benchmarks_GHZzero)
{
    std::string sss(__FILE__);
    std::string benchmarks = sss.substr(0, sss.find_last_of("\\/")) + "/../benchmarks/_all/GHZzero/";
    for (const auto &entry : fs::directory_iterator(benchmarks)) {
        if (!entry.is_directory() || std::stoi(entry.path().string().substr(entry.path().string().find_last_of('/') + 1)) > 6) continue;
        auto folder = entry.path().string();
        auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.spec");
        auto spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.spec");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
        aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.hsl");
        spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.hsl");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
    }
}

BOOST_AUTO_TEST_CASE(benchmarks_GHZall)
{
    std::string sss(__FILE__);
    std::string benchmarks = sss.substr(0, sss.find_last_of("\\/")) + "/../benchmarks/_all/GHZall/";
    for (const auto &entry : fs::directory_iterator(benchmarks)) {
        if (!entry.is_directory() || std::stoi(entry.path().string().substr(entry.path().string().find_last_of('/') + 1)) > 6) continue;
        auto folder = entry.path().string();
        auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.spec");
        auto spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.spec");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
        aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.hsl");
        spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.hsl");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
    }
}

BOOST_AUTO_TEST_CASE(benchmarks_H2)
{
    std::string sss(__FILE__);
    std::string benchmarks = sss.substr(0, sss.find_last_of("\\/")) + "/../benchmarks/_all/H2/";
    for (const auto &entry : fs::directory_iterator(benchmarks)) {
        if (!entry.is_directory() || std::stoi(entry.path().string().substr(entry.path().string().find_last_of('/') + 1)) > 6) continue;
        auto folder = entry.path().string();
        auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.spec");
        auto spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.spec");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
        aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.hsl");
        spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.hsl");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
    }
}

BOOST_AUTO_TEST_CASE(benchmarks_MCToffoli)
{
    std::string sss(__FILE__);
    std::string benchmarks = sss.substr(0, sss.find_last_of("\\/")) + "/../benchmarks/_all/MCToffoli/";
    for (const auto &entry : fs::directory_iterator(benchmarks)) {
        if (!entry.is_directory() || std::stoi(entry.path().string().substr(entry.path().string().find_last_of('/') + 1)) > 6) continue;
        auto folder = entry.path().string();
        auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.spec");
        auto spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.spec");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
        aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.hsl");
        spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.hsl");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
        aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre0.spec");
        spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post0.spec");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
        aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre0.hsl");
        spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post0.hsl");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
        aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre1.spec");
        spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post1.spec");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
        aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre1.hsl");
        spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post1.hsl");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
    }
}

BOOST_AUTO_TEST_CASE(benchmarks_Grover)
{
    std::string sss(__FILE__);
    std::string benchmarks = sss.substr(0, sss.find_last_of("\\/")) + "/../benchmarks/_all/Grover/";
    for (const auto &entry : fs::directory_iterator(benchmarks)) {
        if (!entry.is_directory() || std::stoi(entry.path().string().substr(entry.path().string().find_last_of('/') + 1)) > 6) continue;
        auto folder = entry.path().string();
        auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.spec");
        auto spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.spec");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
        // aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.hsl");
        // spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.hsl");
        // aut.execute(folder + "/circuit.qasm");
        // BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
    }
}

BOOST_AUTO_TEST_CASE(benchmarks_MOGrover)
{
    std::string sss(__FILE__);
    std::string benchmarks = sss.substr(0, sss.find_last_of("\\/")) + "/../benchmarks/_all/MOGrover/";
    for (const auto &entry : fs::directory_iterator(benchmarks)) {
        if (!entry.is_directory() || std::stoi(entry.path().string().substr(entry.path().string().find_last_of('/') + 1)) > 6) continue;
        auto folder = entry.path().string();
        auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.spec");
        auto spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.spec");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
        // aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.hsl");
        // spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.hsl");
        // aut.execute(folder + "/circuit.qasm");
        // BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
    }
}

BOOST_AUTO_TEST_CASE(benchmarks_GroverSym)
{
    std::string sss(__FILE__);
    std::string benchmarks = sss.substr(0, sss.find_last_of("\\/")) + "/../benchmarks/_all/GroverSym/";
    for (const auto &entry : fs::directory_iterator(benchmarks)) {
        if (!entry.is_directory() || std::stoi(entry.path().string().substr(entry.path().string().find_last_of('/') + 1)) > 6) continue;
        auto folder = entry.path().string();
        auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadAutomaton(folder + "/pre.spec");
        auto spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>::ReadAutomaton(folder + "/post.spec");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(AUTOQ::check_inclusion(AUTOQ::Constraint(aut.constraints.c_str()), aut, spec), folder + " failed!");
        // aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.hsl");
        // spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.hsl");
        // aut.execute(folder + "/circuit.qasm");
        // BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
    }
}

BOOST_AUTO_TEST_CASE(benchmarks_MOGroverSym)
{
    std::string sss(__FILE__);
    std::string benchmarks = sss.substr(0, sss.find_last_of("\\/")) + "/../benchmarks/_all/MOGroverSym/";
    for (const auto &entry : fs::directory_iterator(benchmarks)) {
        if (!entry.is_directory() || std::stoi(entry.path().string().substr(entry.path().string().find_last_of('/') + 1)) > 6) continue;
        auto folder = entry.path().string();
        auto aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Symbolic>::ReadAutomaton(folder + "/pre.spec");
        auto spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Predicate>::ReadAutomaton(folder + "/post.spec");
        aut.execute(folder + "/circuit.qasm");
        BOOST_REQUIRE_MESSAGE(AUTOQ::check_inclusion(AUTOQ::Constraint(aut.constraints.c_str()), aut, spec), folder + " failed!");
        // aut = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/pre.hsl");
        // spec = AUTOQ::Parsing::TimbukParser<AUTOQ::Symbol::Concrete>::ReadAutomaton(folder + "/post.hsl");
        // aut.execute(folder + "/circuit.qasm");
        // BOOST_REQUIRE_MESSAGE(aut <= spec, folder + " failed!");
    }
}

// BOOST_AUTO_TEST_SUITE_END()
