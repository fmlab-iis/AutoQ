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

const string &path_to_VATA = "/home/alan23273850/libvata/build/cli/vata";
int size = 5; // the number of qubits.

BOOST_AUTO_TEST_CASE(Z_gate_twice_to_identity)
{
    VATA::Serialization::TimbukSerializer serializer;
    for (const auto &before : {VATA::Util::TreeAutomata::uniform(size), VATA::Util::TreeAutomata::classical(size)}) {
        VATA::Util::TreeAutomata after = before;

        ofstream file1("/tmp/automata1.txt");
        file1 << serializer.Serialize(before);
        file1.close();

        for (int i=0; i<2; i++) {
            after.Z(size/2);

            ofstream file2("/tmp/automata2.txt");
            file2 << serializer.Serialize(after);
            file2.close();

            string include1, include2;
            VATA::Util::ShellCmd(path_to_VATA + " incl /tmp/automata1.txt /tmp/automata2.txt", include1);
            VATA::Util::ShellCmd(path_to_VATA + " incl /tmp/automata2.txt /tmp/automata1.txt", include2);

            if (i < 2-1)
                BOOST_REQUIRE_MESSAGE(!(include1=="1\n" && include2=="1\n"), "");
            else
                BOOST_REQUIRE_MESSAGE(include1=="1\n" && include2=="1\n", "");
        }
    }
}

BOOST_AUTO_TEST_CASE(S_gate_fourth_to_identity)
{
    VATA::Serialization::TimbukSerializer serializer;
    for (const auto &before : {VATA::Util::TreeAutomata::uniform(size), VATA::Util::TreeAutomata::classical(size)}) {
        VATA::Util::TreeAutomata after = before;

        ofstream file1("/tmp/automata1.txt");
        file1 << serializer.Serialize(before);
        file1.close();

        for (int i=0; i<4; i++) {
            after.S(size/2);

            ofstream file2("/tmp/automata2.txt");
            file2 << serializer.Serialize(after);
            file2.close();

            string include1, include2;
            VATA::Util::ShellCmd(path_to_VATA + " incl /tmp/automata1.txt /tmp/automata2.txt", include1);
            VATA::Util::ShellCmd(path_to_VATA + " incl /tmp/automata2.txt /tmp/automata1.txt", include2);

            if (i < 4-1)
                BOOST_REQUIRE_MESSAGE(!(include1=="1\n" && include2=="1\n"), "");
            else
                BOOST_REQUIRE_MESSAGE(include1=="1\n" && include2=="1\n", "");
        }
    }
}

BOOST_AUTO_TEST_CASE(T_gate_eighth_to_identity)
{
    VATA::Serialization::TimbukSerializer serializer;
    for (const auto &before : {VATA::Util::TreeAutomata::uniform(size), VATA::Util::TreeAutomata::classical(size)}) {
        VATA::Util::TreeAutomata after = before;

        ofstream file1("/tmp/automata1.txt");
        file1 << serializer.Serialize(before);
        file1.close();

        for (int i=0; i<8; i++) {
            after.T(size/2);

            ofstream file2("/tmp/automata2.txt");
            file2 << serializer.Serialize(after);
            file2.close();

            string include1, include2;
            VATA::Util::ShellCmd(path_to_VATA + " incl /tmp/automata1.txt /tmp/automata2.txt", include1);
            VATA::Util::ShellCmd(path_to_VATA + " incl /tmp/automata2.txt /tmp/automata1.txt", include2);

            if (i < 8-1)
                BOOST_REQUIRE_MESSAGE(!(include1=="1\n" && include2=="1\n"), "");
            else
                BOOST_REQUIRE_MESSAGE(include1=="1\n" && include2=="1\n", "");
        }
    }
}

BOOST_AUTO_TEST_CASE(CZ_gate_twice_to_identity)
{
    VATA::Serialization::TimbukSerializer serializer;
    for (const auto &before : {VATA::Util::TreeAutomata::uniform(size), VATA::Util::TreeAutomata::classical(size)}) {
        VATA::Util::TreeAutomata after = before;

        ofstream file1("/tmp/automata1.txt");
        file1 << serializer.Serialize(before);
        file1.close();

        for (int i=0; i<2; i++) {
            after.CZ(size*2/3, size/3);

            ofstream file2("/tmp/automata2.txt");
            file2 << serializer.Serialize(after);
            file2.close();

            string include1, include2;
            VATA::Util::ShellCmd(path_to_VATA + " incl /tmp/automata1.txt /tmp/automata2.txt", include1);
            VATA::Util::ShellCmd(path_to_VATA + " incl /tmp/automata2.txt /tmp/automata1.txt", include2);

            if (i < 2-1)
                BOOST_REQUIRE_MESSAGE(!(include1=="1\n" && include2=="1\n"), "");
            else
                BOOST_REQUIRE_MESSAGE(include1=="1\n" && include2=="1\n", "");
        }
    }
}