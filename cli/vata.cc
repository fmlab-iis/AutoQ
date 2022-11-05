#include <fstream>
#include <iostream>
#include <vata/parsing/timbuk_parser.hh>
#include <vata/serialization/timbuk_serializer.hh>
#include <vata/util/aut_description.hh>
#include <vata/util/util.hh>
#include <sys/wait.h>
#include <unistd.h>

#include <chrono>
#include <iomanip>
#include <regex>

using namespace std;
using VATA::Util::TreeAutomata;
using VATA::Util::ShellCmd;
using VATA::Util::ReadFile;

int type, n;

int rand_gen();
void rand_gen(int &a, int &b);
void rand_gen(int &a, int &b, int &c);
std::string toString(std::chrono::steady_clock::duration tp);
void produce_BernsteinVazirani_post();

int main(int argc, char **argv) {
    VATA::Util::TreeAutomata aut = VATA::Parsing::TimbukParser::FromFileToAutomata(argv[1]);
    int stateBefore = aut.stateNum, transitionBefore = aut.transition_size();
    auto startSim = chrono::steady_clock::now();
    string line;
    ifstream qasm(argv[2]);
    const std::regex digit("\\d+");
    const std::regex_iterator<std::string::iterator> END;
    if (!qasm.is_open()) return EXIT_FAILURE;
    while (getline(qasm, line)) {
        if (line.find("OPENQASM") == 0 || line.find("include ") == 0) continue;
        if (line.find("qreg ") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            while (it != END) {
                if (atoi(it->str().c_str()) != aut.qubitNum)
                    throw std::exception();
                ++it;
            }
        } else if (line.find("x ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                aut.X(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("y ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                aut.Y(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("z ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                aut.Z(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("h ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                aut.H(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("s ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                aut.S(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("t ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                aut.T(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("rx(pi/2) ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                aut.Rx(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("ry(pi/2) ") == 0) {
            std::smatch match_pieces;
            if (std::regex_search(line, match_pieces, digit))
                aut.Ry(1 + atoi(match_pieces[0].str().c_str()));
        } else if (line.find("cx ") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            aut.CNOT(pos[0], pos[1]);
        } else if (line.find("cz ") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            aut.CZ(pos[0], pos[1]);
        } else if (line.find("ccx ") == 0) {
            std::regex_iterator<std::string::iterator> it(line.begin(), line.end(), digit);
            std::vector<int> pos;
            while (it != END) {
                pos.push_back(1 + atoi(it->str().c_str()));
                ++it;
            }
            aut.Toffoli(pos[0], pos[1], pos[2]);
        } else if (line.length() > 0)
            throw std::runtime_error("Unsupported gate: " + line);
    }
    qasm.close();
    auto durationSim = chrono::steady_clock::now() - startSim;
    
    auto durationVer = durationSim; // just borrow its type!
    std::ofstream fileLhs(argv[3]);
    aut.fraction_simplication();
    fileLhs << VATA::Serialization::TimbukSerializer::Serialize(aut);
    fileLhs.close(); // Notice that we assume fractions in argv[4] are already simplified.
    auto startVer = chrono::steady_clock::now();
    if (argc >= 5) {
        if (!VATA::Util::TreeAutomata::check_inclusion(argv[3], argv[4])) {
            // throw std::runtime_error("Does not satisfy the postcondition!");
            std::cout << VATA::Util::Convert::ToString(aut.qubitNum) << " & " << VATA::Util::TreeAutomata::gateCount
            << " & " << stateBefore << " & " << aut.stateNum
            << " & " << transitionBefore << " & " << aut.transition_size()
            << " & " << toString(durationSim) << " & V";
            return 0;
        }
    }
    durationVer = chrono::steady_clock::now() - startVer;
    
    std::cout << VATA::Util::Convert::ToString(aut.qubitNum) << " & " << VATA::Util::TreeAutomata::gateCount
        << " & " << stateBefore << " & " << aut.stateNum
        << " & " << transitionBefore << " & " << aut.transition_size()
        << " & " << toString(durationSim) << " & " << toString(durationVer);
    return 0;
}

int rand_gen() {
    if (type == 3) return 1;
    else if (type == 5) return n;
    else return rand() % n + 1;
}
void rand_gen(int &a, int &b) {
    if (type == 3) { // TOP
        a = 1;
        b = 2;
    } else if (type == 5) { // BOTTOM
        a = n-1;
        b = n;
    } else {
        a = rand() % n + 1;
        do {
            b = rand() % n + 1;
        } while (b == a);
    }
}
void rand_gen(int &a, int &b, int &c) {
    if (type == 3) { // TOP
        a = 1;
        b = 2;
        c = 3;
    } else if (type == 5) { // BOTTOM
        a = n-2;
        b = n-1;
        c = n;
    } else {
        a = rand() % n + 1;
        do {
            b = rand() % n + 1;
        } while (b == a);
        do {
            c = rand() % n + 1;
        } while (c == a || c == b);
    }
}

std::string toString(std::chrono::steady_clock::duration tp) {
    using namespace std;
    using namespace std::chrono;
    nanoseconds ns = duration_cast<nanoseconds>(tp);
    typedef duration<int, ratio<86400>> days;
    std::stringstream ss;
    char fill = ss.fill();
    ss.fill('0');
    auto d = duration_cast<days>(ns);
    ns -= d;
    auto h = duration_cast<hours>(ns);
    ns -= h;
    auto m = duration_cast<minutes>(ns);
    ns -= m;
    auto s = duration_cast<seconds>(ns);
    ns -= s;
    auto ms = duration_cast<milliseconds>(ns);
    // auto s = duration<float, std::ratio<1, 1>>(ns);
    if (d.count() > 0 || h.count() > 0)
        ss << "TOO_LONG & ";
    else if (m.count() == 0 && s.count() < 10) {
        ss << s.count() << '.' << ms.count() / 100 << "s";
    } else {
        if (m.count() > 0) ss << m.count() << 'm';
        ss << s.count() << 's';// << " & ";
    }
    ss.fill(fill);
    return ss.str();
}

void produce_BernsteinVazirani_post() {
    for (int n=1; n<=99; n++) {
        VATA::Util::TreeAutomata ans;
        ans.name = "Bernstein-Vazirani";
        ans.qubitNum = n+1;
        assert(ans.qubitNum >= 2);
        ans.finalStates.push_back(0);
        //
        ans.transitions[{1}][{1, 2}] = {0};
        for (int level=2; level<=n; level++) { /* Note that < does not include ans.qubitNum! */
            ans.transitions[{level}][{2*level - 1, 2*level - 1}] = {2*level - 3};
            if (level & 1)
                ans.transitions[{level}][{2*level - 1, 2*level}] = {2*level - 2};
            else
                ans.transitions[{level}][{2*level, 2*level - 1}] = {2*level - 2};
        }
        ans.transitions[{n+1}][{2*(n+1) - 1, 2*(n+1) - 1}] = {2*(n+1) - 3};
        ans.transitions[{n+1}][{2*(n+1) - 1, 2*(n+1)}] = {2*(n+1) - 2};
        //
        ans.transitions[{0,0,0,0,0}][{}] = {2*(n+1) - 1};
        ans.transitions[{1,0,0,0,0}][{}] = {2*(n+1)};
        ans.stateNum = 2*(n+1) + 1;

        std::ofstream of("/tmp/automaton.aut");
        of << VATA::Serialization::TimbukSerializer::Serialize(ans);
        of.close();
        if (n < 10)
            system(("/home/alan23273850/libvata/build/cli/vata red /tmp/automaton.aut > benchmarks/BernsteinVazirani/0" + std::to_string(n) + "/post.aut").c_str());
        else
            system(("/home/alan23273850/libvata/build/cli/vata red /tmp/automaton.aut > benchmarks/BernsteinVazirani/" + std::to_string(n) + "/post.aut").c_str());
    }
    system("rm /tmp/automaton.aut");
}