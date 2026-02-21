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
#include "autoq/parsing/timbuk_parser_util.hh"

namespace AUTOQ {
namespace Parsing {

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
