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
        for (const auto &cl : s.complex) { // cl: complex -> linear combination
            std::string exprR = "0";
            std::string exprI = "0";
            for (const auto &kv : cl.second) { // kv: variable -> integer
                if (kv.first == std::string("1"))
                    exprR = "(+ " + exprR + " (* " + kv.second.str() + " " + kv.first + "))";
                else {
                    exprR = "(+ " + exprR + " (* " + kv.second.str() + " " + kv.first + "R))";
                    exprI = "(+ " + exprI + " (* " + kv.second.str() + " " + kv.first + "I))";
                }
            }
            result["\\$R"] = "(+ " + result["\\$R"] + " (* " + cl.first.realToSMT() + " " + exprR + "))";
            result["\\$R"] = "(- " + result["\\$R"] + " (* " + cl.first.imagToSMT() + " " + exprI + "))";
            result["\\$I"] = "(+ " + result["\\$I"] + " (* " + cl.first.realToSMT() + " " + exprI + "))";
            result["\\$I"] = "(+ " + result["\\$I"] + " (* " + cl.first.imagToSMT() + " " + exprR + "))";
        }
        return result;
    }
};

namespace AUTOQ {
    bool check_inclusion(const Constraint &C, SymbolicAutomata Ae, PredicateAutomata As);
    bool check_validity(Constraint C, const PredicateAutomata::Symbol &ps, const SymbolicAutomata::Symbol &te);
}

#endif