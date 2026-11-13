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
        std::string::size_type line_start = 0;
        if (pos > 0) {
            const std::string::size_type nl = s.rfind('\n', pos - 1);
            line_start = (nl == std::string::npos) ? 0 : nl + 1;
        }
        bool only_comment = true;
        for (std::string::size_type i = line_start; i < pos; ++i) {
            const char c = s[i];
            if (c != ' ' && c != '\t' && c != '\r') {
                only_comment = false;
                break;
            }
        }
        const std::string::size_type end = s.find('\n', pos);
        if (end == std::string::npos) {
            s.erase(only_comment ? line_start : pos);
            break;
        }
        if (only_comment) {
            // A comment-only line is removed entirely. Leaving the newline
            // would make a blank line, which the Constraints parser rejects.
            s.erase(line_start, end - line_start + 1);
            pos = line_start;
        } else {
            // Keep the newline. Erasing it joins the next line onto this one (#28).
            s.erase(pos, end - pos);
        }
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
