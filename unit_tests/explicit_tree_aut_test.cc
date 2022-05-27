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

bool check_equal_aut(const VATA::Util::TreeAutomata& lhs, const VATA::Util::TreeAutomata& rhs)
{
	VATA::Serialization::TimbukSerializer serializer;
	std::ofstream fileLhs("/tmp/automata1.txt");
	fileLhs << serializer.Serialize(lhs);
	fileLhs.close();

	std::ofstream fileRhs("/tmp/automata2.txt");
	fileRhs << serializer.Serialize(rhs);
	fileRhs.close();

	return check_equal("/tmp/automata1.txt", "/tmp/automata2.txt");
}


BOOST_AUTO_TEST_CASE(X_gate_twice_to_identity)
{
    int n = size/2 + 1;
    VATA::Serialization::TimbukSerializer serializer;
    for (const auto &before : {VATA::Util::TreeAutomata::uniform(n), VATA::Util::TreeAutomata::classical(n)}) {

        for (auto t : {1, n/2+1, n}) {
            VATA::Util::TreeAutomata after = before;
            for (int i=0; i<2; i++) {
                after.X(t);

                if (i < 2-1) {}
                    // BOOST_REQUIRE_MESSAGE(!(include1=="1\n" && include2=="1\n"), "");
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

        for (auto t : {1, n/2+1, n}) {
            VATA::Util::TreeAutomata after = before;
            for (int i=0; i<2; i++) {
                after.Y(t);

                if (i < 2-1) {
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

        for (int i=0; i<2; i++) {
            after.Z(size/2);

            if (i < 2-1) {
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

        for (auto t : {1, n/2+1, n}) {
            VATA::Util::TreeAutomata after = before;
            for (int i=0; i<2; i++) {
								after.H(t);

								if (i < 2-1) {
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

        for (int i=0; i<4; i++) {
            after.S(size/2);

            if (i < 4-1) {
								BOOST_REQUIRE_MESSAGE(!check_equal_aut(before, after), "");
						}
						else {
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

        for (int i=0; i<8; i++) {
            after.T(size/2);

            if (i < 8-1) {
								BOOST_REQUIRE_MESSAGE(!check_equal_aut(before, after), "");
						}
						else {
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

        for (int i=0; i<2; i++) {
            after.CZ(size*2/3, size/3);

            if (i < 2-1) {
								BOOST_REQUIRE_MESSAGE(!check_equal_aut(before, after), "");
						}
						else {
								BOOST_REQUIRE_MESSAGE(check_equal_aut(before, after), "");
						}
        }
    }
}
