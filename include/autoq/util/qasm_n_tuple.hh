#ifndef _AUTOQ_UTIL_QASM_N_TUPLE_HH_
#define _AUTOQ_UTIL_QASM_N_TUPLE_HH_

#include <autoq/complex/complex.hh>
#include <autoq/complex/ntuple.hh>
#include <autoq/error.hh>
#include <autoq/error_messages.hh>
#include <autoq/parsing/angle.hh>
#include <autoq/util/qasm_regex.hh>
#include <autoq/util/string.hh>
#include <fstream>
#include <string>

namespace AUTOQ {

/** One-pass scan of a QASM file to set nTuple::N from gate set (only when Complex == nTuple). */
inline void adjust_N_in_nTuple(const std::string& filename) {
    if constexpr (!std::is_same_v<AUTOQ::Complex::Complex, AUTOQ::Complex::nTuple>) return;
    using NType = decltype(AUTOQ::Complex::nTuple::N);
    static const std::pair<const char*, NType> kGateMinN[] = {
        {"y ", 2}, {"s ", 2}, {"sdg ", 2}, {"t ", 4}, {"tdg ", 4}};
    auto update_N_from_angle = [](const std::string& angle_str, const char* gate_name) {
        auto half_turns =
            AUTOQ::Parsing::parse_angle_to_rational(angle_str, gate_name, "1") / 2;
        if (AUTOQ::Complex::nTuple::N < static_cast<NType>(half_turns.denominator())) {
            AUTOQ::Complex::nTuple::N = static_cast<NType>(half_turns.denominator());
        }
    };
    std::ifstream qasm(filename);
    const AUTOQ::QasmRegexes re;
    if (!qasm.is_open())
        THROW_AUTOQ_ERROR(std::string(ErrorMessages::kOpenFilePrefix) + filename + ".");
    std::string line;
    while (std::getline(qasm, line)) {
        line = AUTOQ::String::trim(line);
        std::smatch match_rx;
        std::regex_search(line, match_rx, re.rx);
        std::smatch match_rz;
        std::regex_search(line, match_rz, re.rz);
        if (line.find("OPENQASM") == 0 || line.find("include ") == 0 ||
            line.find("//") == 0)
            continue;
        if (line.find("qreg ") == 0) {
        } else if (line.find("x ") == 0 || line.find("z ") == 0 || line.find("h ") == 0) {
        } else {
            bool gate_min_n_done = false;
            for (const auto& [prefix, min_n] : kGateMinN) {
                if (line.find(prefix) == 0) {
                    if (AUTOQ::Complex::nTuple::N < min_n)
                        AUTOQ::Complex::nTuple::N = min_n;
                    gate_min_n_done = true;
                    break;
                }
            }
            if (!gate_min_n_done) {
                if (match_rx.size() == 3) {
                    update_N_from_angle(match_rx[1].str(), "rx");
                } else if (match_rz.size() == 3) {
                    update_N_from_angle(match_rz[1].str(), "rz");
                } else if (line.find("ry(pi/2) ") == 0 || line.find("ry(pi / 2)") == 0) {
                } else if (line.find("cx ") == 0 || line.find("CX ") == 0) {
                } else if (line.find("cz ") == 0) {
                } else if (line.find("for ") == 0) {
                } else if (line.find("}") == 0) {
                } else if (line.find("ccx ") == 0) {
                } else if (line.find("swap ") == 0) {
                } else if (line.find("PRINT_STATS") == 0) {
                } else if (line.find("PRINT_AUT") == 0) {
                } else if (line.find("STOP") == 0) {
                }
            }
        }
    }
}

}  // namespace AUTOQ

#endif
