/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Description:
 *    Implementation of Timbuk parser utilities.
 *****************************************************************************/

#include <fstream>
#include <filesystem>
#include <regex>

#include "autoq/error.hh"
#include "autoq/util/string.hh"
#include "autoq/parsing/parser/timbuk_parser_util.hh"

namespace AUTOQ {
namespace Parsing {

void strip_line_comments(std::string& s) {
    std::string::size_type pos = 0;
    while ((pos = s.find("//", pos)) != std::string::npos) {
        std::string::size_type end = s.find('\n', pos);
        if (end == std::string::npos) {
            s.erase(pos);
            break;
        }
        s.erase(pos, end - pos + 1);
    }
}

std::pair<std::string, std::string> split_automaton_and_constraints(const std::string& fileContents) {
    const size_t found = fileContents.find("Constraints");
    if (found != std::string::npos) {
        return {fileContents.substr(0, found), fileContents.substr(found + 11)};
    }
    return {fileContents, ""};
}

std::vector<std::string> find_all_loop_invariants(const char* filename) {
    std::ifstream qasm(filename);
    if (!qasm.is_open())
        THROW_AUTOQ_ERROR("Failed to open file " + std::string(filename) + ".");
    std::string line;
    std::vector<std::string> list;
    while (getline(qasm, line)) {
        line = AUTOQ::String::trim(line);
        if (line.find("while") == 0) {
            const std::regex spec("// *(.*)");
            std::regex_iterator<std::string::iterator> it2(line.begin(), line.end(), spec);
            std::string dir = (std::filesystem::current_path() / filename).parent_path().string();
            list.push_back(dir + std::string("/") + it2->str(1));
        }
    }
    qasm.close();
    return list;
}

}  // namespace Parsing
}  // namespace AUTOQ
