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
#include <vata/util/aut_description.hh>
#include <vata/serialization/timbuk_serializer.hh>

#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE AutType
#include <boost/test/unit_test.hpp>

int size = 10;

bool shellCmd(const string &cmd, string &result) {
    char buffer[512];
    result = "";

    // Open pipe to file
    FILE* pipe = popen(cmd.c_str(), "r");
    if (!pipe) {
        return false;
    }

    // read till end of process:
    while (!feof(pipe)) {
        // use buffer to read and add to result
        if (fgets(buffer, sizeof(buffer), pipe) != NULL)
            result += buffer;
    }

    pclose(pipe);
    return true;
}

VATA::Util::TreeAutomata uniform(int n) {
    VATA::Util::TreeAutomata aut;
    aut.name = "Uniform";
    int pow_of_two = 1;
    int state_counter = 0;
    for (int level=1; level<=n; level++) {
        for (int i=0; i<pow_of_two; i++) {
            if (level < n)
                aut.transitions[{level}][{state_counter*2+1, state_counter*2+2}] = {state_counter};
            else
                aut.transitions[{level}][{pow_of_two*2-1, pow_of_two*2-1}].insert(state_counter);
            aut.symbols[{level}] = 2;
            state_counter++;
        }
        pow_of_two *= 2;
    }
    aut.transitions[{1,0,0,0,n}][{}] = {pow_of_two-1};
    aut.symbols[{1,0,0,0,n}] = 0;
	aut.finalStates.insert(0);
    aut.stateNum = pow_of_two;

    aut.determinize();
    aut.minimize();
    return aut;
}

BOOST_AUTO_TEST_CASE(Z_gate_twice_to_identity)
{
    VATA::Serialization::TimbukSerializer serializer;
    VATA::Util::TreeAutomata before = uniform(size);
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
        shellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata1.txt /tmp/automata2.txt", include1);
        shellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata2.txt /tmp/automata1.txt", include2);

        if (i < 2-1)
            BOOST_REQUIRE_MESSAGE(!(include1=="1\n" && include2=="1\n"), "");
        else
            BOOST_REQUIRE_MESSAGE(include1=="1\n" && include2=="1\n", "");
    }    
}

BOOST_AUTO_TEST_CASE(S_gate_fourth_to_identity)
{
    VATA::Serialization::TimbukSerializer serializer;
    VATA::Util::TreeAutomata before = uniform(size);
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
        shellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata1.txt /tmp/automata2.txt", include1);
        shellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata2.txt /tmp/automata1.txt", include2);

        if (i < 4-1)
            BOOST_REQUIRE_MESSAGE(!(include1=="1\n" && include2=="1\n"), "");
        else
            BOOST_REQUIRE_MESSAGE(include1=="1\n" && include2=="1\n", "");
    }
}

BOOST_AUTO_TEST_CASE(T_gate_eighth_to_identity)
{
    VATA::Serialization::TimbukSerializer serializer;
    VATA::Util::TreeAutomata before = uniform(size);
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
        shellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata1.txt /tmp/automata2.txt", include1);
        shellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata2.txt /tmp/automata1.txt", include2);

        if (i < 8-1)
            BOOST_REQUIRE_MESSAGE(!(include1=="1\n" && include2=="1\n"), "");
        else
            BOOST_REQUIRE_MESSAGE(include1=="1\n" && include2=="1\n", "");
    }
}

BOOST_AUTO_TEST_CASE(CZ_gate_twice_to_identity)
{
    VATA::Serialization::TimbukSerializer serializer;
    VATA::Util::TreeAutomata before = uniform(size);
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
        shellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata1.txt /tmp/automata2.txt", include1);
        shellCmd("/home/alan23273850/libvata/build/cli/vata incl /tmp/automata2.txt /tmp/automata1.txt", include2);

        if (i < 2-1)
            BOOST_REQUIRE_MESSAGE(!(include1=="1\n" && include2=="1\n"), "");
        else
            BOOST_REQUIRE_MESSAGE(include1=="1\n" && include2=="1\n", "");
    }    
}