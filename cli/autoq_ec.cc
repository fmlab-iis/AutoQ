#include <fstream>
#include <iostream>
#include <autoq/parsing/timbuk_parser.hh>
#include <autoq/serialization/timbuk_serializer.hh>
#include <autoq/aut_description.hh>
#include <autoq/inclusion.hh>
#include <autoq/util/util.hh>
#include <util_sim.h>
#include <sys/wait.h>
#include <unistd.h>

#include <chrono>
#include <iomanip>
#include <regex>

using namespace std;
using AUTOQ::TreeAutomata;
using AUTOQ::Util::ShellCmd;
using AUTOQ::Util::ReadFile;

std::string toString(std::chrono::steady_clock::duration tp);

int extract_qubit(const std::string& filename) {
    std::ifstream file(filename);
    if (!file.is_open()) {
        std::cerr << "Unable to open file" << std::endl;
        return -1; // Indicate an error opening the file
    }

    std::string line;
    std::regex pattern(R"(qreg\s+\w+\[(\d+)\];)");
    std::smatch match;
    while (std::getline(file, line)) {
        if (std::regex_search(line, match, pattern)) {
            return std::stoi(match[1].str());
        }
    }

    std::cerr << "Pattern not found" << std::endl;
    return -1; // Indicate that the pattern was not found
}

int main(int argc, char **argv) {
try {
    auto startVer = chrono::steady_clock::now();
    AUTOQ::TreeAutomata aut = AUTOQ::TreeAutomata::prefix_basis(extract_qubit(argv[1]));
    aut.execute(argv[1]);
    AUTOQ::TreeAutomata aut2 = AUTOQ::TreeAutomata::prefix_basis(extract_qubit(argv[2]));
    aut2.execute(argv[2]);
    bool result = AUTOQ::TreeAutomata::check_inclusion(aut, aut2);
    std::cout << toString(chrono::steady_clock::now() - startVer) << " & " << (result ? "F" : "T") << "\n";
    return 0;
} catch (std::exception &e) {
    std::cout << e.what() << std::endl;
    return 0;
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
    if (d.count() > 0)
        ss << d.count() << 'd' << h.count() << 'h' << m.count() << 'm' << s.count() << 's';
    else if (h.count() > 0)
        ss << h.count() << 'h' << m.count() << 'm' << s.count() << 's';
    else if (m.count() == 0 && s.count() < 10) {
        ss << s.count() << '.' << ms.count() / 100 << "s";
    } else {
        if (m.count() > 0) ss << m.count() << 'm';
        ss << s.count() << 's';// << " & ";
    }
    ss.fill(fill);
    return ss.str();
}
