#ifndef _AUTOQ_INCLUSION_HH_
#define _AUTOQ_INCLUSION_HH_

#include <regex>
#include <string>
#include <vector>
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
    std::vector<std::string> to_exprs(Symbol::Symbolic s) {
        assert(s.size() == 5);
        std::vector<std::string> result;
        for (int i=0; i<4; i++) {
            std::string expr = "0";
            for (const auto &kv : s.at(i)) {
                expr = "(+ " + expr + " (* " + kv.second.str() + " " + kv.first + "))";
            }
            expr = "(/ " + expr + " (pow_sqrt2_k " + s.at(4)["1"].str() + "))";
            result.push_back(expr);
            content.append("(assert (= ");
            content.append(boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>(s.at(4)["1"])).convert_to<std::string>());
            content.append(std::regex_replace(" (* (pow_sqrt2_k $) (pow_sqrt2_k $))))(assert (>= (pow_sqrt2_k $) 0))", std::regex("\\$"), s.at(4)["1"].str()));
        }
        content = "(declare-fun pow_sqrt2_k (Int) Real)" + content;
        return result;
    }
};

namespace AUTOQ {
    bool is_spec_satisfied(const Constraint &C, const SymbolicAutomata &Ae, const PredicateAutomata &As);
    bool check_validity(Constraint C, const PredicateAutomata::InitialSymbol &ps, const SymbolicAutomata::InitialSymbol &te);
}

#endif