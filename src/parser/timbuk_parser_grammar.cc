/*****************************************************************************
 *  Timbuk parser – Constants section and unify_complex_k (definitions).
 *****************************************************************************/

#include <climits>
#include <sstream>

#include "autoq/error.hh"
#include "autoq/util/string.hh"
#include "autoq/complex/complex.hh"
#include "autoq/parsing/parser/timbuk_parser_util.hh"
#include "autoq/parsing/ExtendedDirac/EvaluationVisitor.h"

namespace AUTOQ {
namespace Parsing {

void parse_constants_section(std::string& fileContents, std::map<std::string, AUTOQ::Complex::Complex>& out_constants) {
    if (fileContents.find("Constants") == std::string::npos) return;
    size_t found2 = std::min({fileContents.find("Extended"), fileContents.find("Root"), fileContents.find("Variable")});
    if (found2 == std::string::npos)
        THROW_AUTOQ_ERROR("Neither \"Extended Dirac\" nor \"Root States\" are specified.");
    std::string constants_str = AUTOQ::String::trim(fileContents.substr(std::string("Constants").length(), found2 - std::string("Constants").length()));
    fileContents = fileContents.substr(found2);
    std::stringstream ss(constants_str);
    std::string str;
    while (std::getline(ss, str, '\n')) {
        size_t arrow_pos = str.find(":=");
        if (std::string::npos != arrow_pos) {
            std::string lhs = AUTOQ::String::trim(str.substr(0, arrow_pos));
            std::string rhs = AUTOQ::String::trim(str.substr(arrow_pos + 2));
            if (lhs.empty() || rhs.empty())
                THROW_AUTOQ_ERROR("Invalid number \"" + str + "\".");
            if (out_constants.find(lhs) == out_constants.end())
                out_constants[lhs] = EvaluationVisitor<>::ComplexParser(rhs).getComplex();
            else
                THROW_AUTOQ_ERROR("The constant \"" + lhs + "\" is already defined.");
        }
    }
}

void unify_complex_k(std::map<std::string, AUTOQ::Complex::Complex>& constants) {
#ifdef COMPLEX_FiveTuple
    boost::multiprecision::cpp_int max_k = INT_MIN;
    for (const auto& kv : constants) {
        if (kv.second.at(0) != 0 || kv.second.at(1) != 0 || kv.second.at(2) != 0 || kv.second.at(3) != 0)
            if (max_k < kv.second.at(4)) max_k = kv.second.at(4);
    }
    if (max_k == INT_MIN) max_k = 0;
    for (auto& kv : constants) {
        if (kv.second.at(0) == 0 && kv.second.at(1) == 0 && kv.second.at(2) == 0 && kv.second.at(3) == 0)
            kv.second.at(4) = max_k;
        else
            kv.second.increase_to_k(max_k);
    }
#endif
#ifdef COMPLEX_nTuple
    boost::multiprecision::cpp_int max_k = INT_MIN;
    for (const auto& kv : constants) {
        if (!kv.second.empty() && max_k < kv.second.k()) max_k = kv.second.k();
    }
    if (max_k == INT_MIN) max_k = 0;
    for (auto& kv : constants) {
        if (kv.second.empty())
            kv.second.k() = max_k;
        else
            kv.second.adjust_k(max_k - kv.second.k());
    }
#endif
}

}  // namespace Parsing
}  // namespace AUTOQ
