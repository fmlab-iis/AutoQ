/*****************************************************************************
 *  VATA Tree Automata Library
 *
 *  Copyright (c) 2011  Ondra Lengal <ilengal@fit.vutbr.cz>
 *
 *  Description:
 *    Test suite for explicit tree automaton
 *
 *****************************************************************************/

// VATA headers
#include <fstream>
#include <vata/vata.hh>
#include <vata/util/util.hh>
#include <vata/util/aut_description.hh>
#include <vata/serialization/timbuk_serializer.hh>

#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE AutType
#include <boost/test/unit_test.hpp>

std::string gpath_to_VATA = "";
int size = 5; // the number of qubits.

/** returns the path to VATA executable */
const std::string& get_vata_path()
{
	// is it cached?
	if (!gpath_to_VATA.empty()) return gpath_to_VATA;

	// not cached, get it from ENV
	const char* path = std::getenv("VATA_PATH");
	if (nullptr == path) {
		throw std::runtime_error("Cannot find environment variable VATA_PATH");
	}

	gpath_to_VATA = path;
	return gpath_to_VATA;
}


/** checks inclusion of two TAs */
bool check_inclusion(const std::string& lhsPath, const std::string& rhsPath)
{
	std::string aux;
	VATA::Util::ShellCmd(get_vata_path() + " incl " + lhsPath + " " + rhsPath, aux);
	return (aux == "1\n");
}

/** checks language equivalence of two TAs */
bool check_equal(const std::string& lhsPath, const std::string& rhsPath)
{
	return check_inclusion(lhsPath, rhsPath) && check_inclusion(rhsPath, lhsPath);
}

bool check_equal_aut(VATA::Util::TreeAutomata lhs, VATA::Util::TreeAutomata rhs)
{
	VATA::Serialization::TimbukSerializer serializer;
	std::ofstream fileLhs("/tmp/automata1.txt");
    lhs.fraction_simplication();
	fileLhs << serializer.Serialize(lhs);
	fileLhs.close();

	std::ofstream fileRhs("/tmp/automata2.txt");
    rhs.fraction_simplication();
	fileRhs << serializer.Serialize(rhs);
	fileRhs.close();

	return check_equal("/tmp/automata1.txt", "/tmp/automata2.txt");
}


BOOST_AUTO_TEST_CASE(X_gate_twice_to_identity)
{
    int n = size/2 + 1;
    VATA::Serialization::TimbukSerializer serializer;
    for (const auto &before : {VATA::Util::TreeAutomata::uniform(n),
                               VATA::Util::TreeAutomata::classical(n),
                               VATA::Util::TreeAutomata::random(n)}) {
        int loop = 2;
        for (auto t : {1, n/2+1, n}) {
            VATA::Util::TreeAutomata after = before;
            for (int i=0; i<loop; i++) {
                after.X(t);

                if (i < loop-1) {
                    if (before.name == "Random")
                        BOOST_REQUIRE_MESSAGE(!check_equal_aut(before, after), "");
                }
                else {
                    BOOST_REQUIRE_MESSAGE(check_equal_aut(before, after), "");
				}
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(Y_gate_twice_to_identity)
{
    int n = size/2 + 1;
    VATA::Serialization::TimbukSerializer serializer;
    for (const auto &before : {VATA::Util::TreeAutomata::uniform(n), VATA::Util::TreeAutomata::classical(n)}) {
        int loop = 2;
        for (auto t : {1, n/2+1, n}) {
            VATA::Util::TreeAutomata after = before;
            for (int i=0; i<loop; i++) {
                after.Y(t);

                if (i < loop-1) {
                    BOOST_REQUIRE_MESSAGE(!check_equal_aut(before, after), "");
				}
                else {
                    BOOST_REQUIRE_MESSAGE(check_equal_aut(before, after), "");
				}
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(Z_gate_twice_to_identity)
{
    VATA::Serialization::TimbukSerializer serializer;
    for (const auto &before : {VATA::Util::TreeAutomata::uniform(size), VATA::Util::TreeAutomata::classical(size)}) {
        VATA::Util::TreeAutomata after = before;
        int loop = 2;
        for (int i=0; i<loop; i++) {
            after.Z(size/2);

            if (i < loop-1) {
                BOOST_REQUIRE_MESSAGE(!check_equal_aut(before, after), "");
			}
            else {
                BOOST_REQUIRE_MESSAGE(check_equal_aut(before, after), "");
			}
        }
    }
}

BOOST_AUTO_TEST_CASE(H_gate_twice_to_identity)
{
    int n = size/2 + 1;
    VATA::Serialization::TimbukSerializer serializer;
    for (const auto &before : {VATA::Util::TreeAutomata::uniform(n), VATA::Util::TreeAutomata::classical(n)}) {
        int loop = 2;
        for (auto t : {1, n/2+1, n}) {
            VATA::Util::TreeAutomata after = before;
            for (int i=0; i<loop; i++) {
                after.H(t);

                if (i < loop-1) {
                    BOOST_REQUIRE_MESSAGE(!check_equal_aut(before, after), "");
                }
                else {
                    BOOST_REQUIRE_MESSAGE(check_equal_aut(before, after), "");
                }
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(S_gate_fourth_to_identity)
{
    VATA::Serialization::TimbukSerializer serializer;
    for (const auto &before : {VATA::Util::TreeAutomata::uniform(size), VATA::Util::TreeAutomata::classical(size)}) {
        VATA::Util::TreeAutomata after = before;
        int loop = 4;
        for (int i=0; i<loop; i++) {
            after.S(size/2);

            if (i < loop-1) {
                BOOST_REQUIRE_MESSAGE(!check_equal_aut(before, after), "");
            } else {
                BOOST_REQUIRE_MESSAGE(check_equal_aut(before, after), "");
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(T_gate_eighth_to_identity)
{
    VATA::Serialization::TimbukSerializer serializer;
    for (const auto &before : {VATA::Util::TreeAutomata::uniform(size), VATA::Util::TreeAutomata::classical(size)}) {
        VATA::Util::TreeAutomata after = before;
        int loop = 8;
        for (int i=0; i<loop; i++) {
            after.T(size/2);

            if (i < loop-1) {
                BOOST_REQUIRE_MESSAGE(!check_equal_aut(before, after), "");
            } else {
                BOOST_REQUIRE_MESSAGE(check_equal_aut(before, after), "");
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(Rx_gate_eighth_to_identity)
{
    int n = size/2 + 1;
    VATA::Serialization::TimbukSerializer serializer;
    for (const auto &before : {VATA::Util::TreeAutomata::uniform(n), VATA::Util::TreeAutomata::classical(n)}) {
        int loop = 8;
        for (auto t : {1, n/2+1, n}) {
            VATA::Util::TreeAutomata after = before;
            for (int i=0; i<loop; i++) {
                after.Rx(t);

                if (i < loop-1) {
                    BOOST_REQUIRE_MESSAGE(!check_equal_aut(before, after), "");
                }
                else {
                    BOOST_REQUIRE_MESSAGE(check_equal_aut(before, after), "");
				}
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(Ry_gate_eighth_to_identity)
{
    int n = size/2 + 1;
    VATA::Serialization::TimbukSerializer serializer;
    for (const auto &before : {VATA::Util::TreeAutomata::uniform(n), VATA::Util::TreeAutomata::classical(n)}) {
        int loop = 8;
        for (auto t : {1, n/2+1, n}) {
            VATA::Util::TreeAutomata after = before;
            for (int i=0; i<loop; i++) {
                after.Ry(t);

                if (i < loop-1) {
                    BOOST_REQUIRE_MESSAGE(!check_equal_aut(before, after), "");
                }
                else {
                    BOOST_REQUIRE_MESSAGE(check_equal_aut(before, after), "");
				}
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(CNOT_gate_twice_to_identity)
{
    int n = size/2 + 1;
    VATA::Serialization::TimbukSerializer serializer;
    for (const auto &before : {VATA::Util::TreeAutomata::uniform(n),
                               VATA::Util::TreeAutomata::classical(n),
                               VATA::Util::TreeAutomata::random(n)}) {
        VATA::Util::TreeAutomata after = before;
        int loop = 2;
        for (int i=0; i<loop; i++) {
            after.CNOT(n*2/3, n/3);

            if (i < loop-1) {
                if (before.name == "Random")
                    BOOST_REQUIRE_MESSAGE(!check_equal_aut(before, after), "");
            } else {
                BOOST_REQUIRE_MESSAGE(check_equal_aut(before, after), "");
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(CZ_gate_twice_to_identity)
{
    VATA::Serialization::TimbukSerializer serializer;
    for (const auto &before : {VATA::Util::TreeAutomata::uniform(size), VATA::Util::TreeAutomata::classical(size)}) {
        VATA::Util::TreeAutomata after = before;
        int loop = 2;
        for (int i=0; i<loop; i++) {
            after.CZ(size*2/3, size/3);

            if (i < loop-1) {
                BOOST_REQUIRE_MESSAGE(!check_equal_aut(before, after), "");
            } else {
                BOOST_REQUIRE_MESSAGE(check_equal_aut(before, after), "");
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(Toffoli_gate_twice_to_identity)
{
    VATA::Serialization::TimbukSerializer serializer;
    for (const auto &before : {VATA::Util::TreeAutomata::uniform(3),
                               VATA::Util::TreeAutomata::classical(3),
                               VATA::Util::TreeAutomata::random(3)}) {
        int v[] = {1,2,3};
        do {
            VATA::Util::TreeAutomata after = before;
            int loop = 2;
            for (int i=0; i<loop; i++) {
                after.Toffoli(v[0], v[1], v[2]);

                if (i < loop-1) {
                    if (before.name == "Random")
                        BOOST_REQUIRE_MESSAGE(!check_equal_aut(before, after), "");
                } else {
                    BOOST_REQUIRE_MESSAGE(check_equal_aut(before, after), "");
                }
            }
        } while (std::next_permutation(v, v+3));
    }
}

BOOST_AUTO_TEST_CASE(Fredkin_gate_twice_to_identity)
{
    VATA::Serialization::TimbukSerializer serializer;
    for (const auto &before : {VATA::Util::TreeAutomata::uniform(3),
                               VATA::Util::TreeAutomata::classical(3),
                               VATA::Util::TreeAutomata::random(3)}) {
        int v[] = {1,2,3};
        do {
            VATA::Util::TreeAutomata after = before;
            int loop = 2;
            for (int i=0; i<loop; i++) {
                after.Fredkin(v[0], v[1], v[2]);

                if (i < loop-1) {
                    BOOST_REQUIRE_MESSAGE(!check_equal_aut(before, after), "");
                } else {
                    BOOST_REQUIRE_MESSAGE(check_equal_aut(before, after), "");
                }
            }
        } while (std::next_permutation(v, v+3));
    }
}

BOOST_AUTO_TEST_CASE(Bernstein_Vazirani)
{
    int n = 4; // 5 is also OK!
    VATA::Serialization::TimbukSerializer serializer;
    auto aut = VATA::Util::TreeAutomata::zero(n+1);

    for (int i=1; i<=n+1; i++) {
        aut.H(i);
    }
    aut.Z(n+1);
    for (int i=1; i<=n; i++) {
        auto aut2 = aut;
        aut2.CNOT(i, n+1);
        aut = aut.Union(aut2);
    }
    for (int i=1; i<=n; i++) {
        aut.H(i);
    }

    VATA::Util::TreeAutomata ans;
    ans.name = "Bernstein-Vazirani";
    ans.qubitNum = n+1;
    assert(ans.qubitNum >= 2);
    ans.finalStates.insert(0);
    for (int level=1; level<ans.qubitNum; level++) { /* Note that < does not include ans.qubitNum! */
        if (level >= 2)
            ans.transitions[{level}][{2*level - 1, 2*level - 1}] = {2*level - 3};
        ans.transitions[{level}][{2*level - 1, 2*level}] = {2*level - 2};
        ans.transitions[{level}][{2*level, 2*level - 1}] = {2*level - 2};
    }
    ans.stateNum = 2*(ans.qubitNum-1) + 1;
    ans.transitions[{0,0,0,0,1}][{}] = {ans.stateNum++};
    ans.transitions[{1,0,0,0,1}][{}] = {ans.stateNum++};
    ans.transitions[{-1,0,0,0,1}][{}] = {ans.stateNum++};
    ans.transitions[{ans.qubitNum}][{ans.stateNum - 3, ans.stateNum - 3}] = {2*(ans.qubitNum-1) - 1};
    ans.transitions[{ans.qubitNum}][{ans.stateNum - 2, ans.stateNum - 1}] = {2*(ans.qubitNum-1)};

    BOOST_REQUIRE_MESSAGE(check_equal_aut(aut, ans), "");
}
