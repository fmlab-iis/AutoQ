#ifndef _AUTOQ_INCLUSION_HH_
#define _AUTOQ_INCLUSION_HH_

#include <regex>
#include <string>
#include <vector>
#include <autoq/complex/complex.hh>
#include <autoq/symbol/symbolic.hh>
#include <autoq/aut_description.hh>

namespace AUTOQ
{
    struct Constraint;
}

struct AUTOQ::Constraint {
    std::string content;
    Constraint(const std::string &s) : content(s) {}
    operator std::string() const { return content; }
    auto to_exprs(const Symbol::Symbolic &s) {
        assert(!s.is_internal());
        std::map<std::string, std::string> result;
        result["\\$R"] = "0";
        result["\\$I"] = "0";
        for (const auto &tc : s.complex) { // tc: term -> complex
            const auto &term = tc.first;
            const auto &value = tc.second;
            result["\\$R"] = "(+ " + result["\\$R"] + " (* " + term.expand() + " " + value.realToSMT() + "))";
            result["\\$I"] = "(+ " + result["\\$I"] + " (* " + term.expand() + " " + value.imagToSMT() + "))";
        }
        return result;
    }
};

namespace AUTOQ {
    bool is_scaled_spec_satisfied(const TreeAutomata &R, TreeAutomata Q);
    bool is_scaled_spec_satisfied(SymbolicAutomata R, SymbolicAutomata Q);
    bool is_spec_satisfied(const Constraint &C, const SymbolicAutomata &Ae, const PredicateAutomata &As);
    bool check_validity(Constraint C, const PredicateAutomata::Symbol &ps, const SymbolicAutomata::Symbol &te);
    bool call_SMT_solver(const std::string &var_defs, const std::string &assertion);
}

#endif
