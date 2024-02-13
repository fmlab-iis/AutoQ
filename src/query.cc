#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/symbol/predicate.hh"
#include "autoq/aut_description.hh"
#include "autoq/serialization/timbuk_serializer.hh"
#include <boost/dynamic_bitset.hpp> // used in print_language

#include "simulation/explicit_lts.hh"

using namespace AUTOQ;
using namespace AUTOQ::Util;
using AUTOQ::Serialization::TimbukSerializer;

template <typename Symbol>
int AUTOQ::Automata<Symbol>::count_states() const {
    int maxState = 0;
    for (const auto &t : transitions) {
        for (const auto &out_ins : t.second) {
            if (maxState < out_ins.first)
                maxState = out_ins.first;
            for (const auto &in : out_ins.second) {
                for (const auto &s : in) {
                    if (maxState < s)
                        maxState = s;
                }
            }
        }
    }
    return maxState + 1;
}

template <typename Symbol>
int AUTOQ::Automata<Symbol>::count_transitions() const {
    int count = 0;
    for (const auto &t : transitions)
        for (const auto &out_ins : t.second) {
            count += out_ins.second.size();
        }
    return count;
}

template <typename Symbol>
void AUTOQ::Automata<Symbol>::print(const std::string &prompt) const {
    std::cout << prompt;
    std::cout << AUTOQ::Serialization::TimbukSerializer::Serialize(*this);
}

template <typename Symbol>
std::vector<std::vector<std::string>> get_all_languages_under_the_state_at_this_level(
    const AUTOQ::Automata<Symbol> * const This,
    int qubit,
    typename AUTOQ::Automata<Symbol>::State state)
{
    if (qubit == static_cast<int>(This->qubitNum + 1)) {
        std::vector<std::vector<std::string>> ans;
        for (const auto &t : This->transitions) { // construct the map from state to leaf symbol
            auto symboltag = t.first;
            if (symboltag.is_leaf()) {
                auto it = t.second.find(state);
                if (it != t.second.end() && !it->second.empty())
                    ans.push_back({symboltag.symbol().str()});
            }
        }
        return ans;
    }
    std::vector<std::vector<std::string>> ans;
    for (const auto &out_ins : This->transitions.at({qubit})) {
        if (out_ins.first == state) {
            for (const auto &in : out_ins.second) {
                auto v1 = get_all_languages_under_the_state_at_this_level<Symbol>(This, qubit + 1, in.at(0));
                auto v2 = get_all_languages_under_the_state_at_this_level<Symbol>(This, qubit + 1, in.at(1));
                for (const auto &s1 : v1) {
                    for (const auto &s2 : v2) {
                        auto v = s1;
                        v.insert(v.end(), s2.begin(), s2.end());
                        ans.push_back(v);
                    }
                }
            }
        }
    }
    return ans;
}
// template <>
// std::vector<std::vector<std::string>> AUTOQ::Automata<Concrete>::get_all_languages_under_the_state_at_this_level(int qubit, typename AUTOQ::Automata<Concrete>::State state) const {
//     if (qubit == static_cast<int>(qubitNum + 1)) {
//         std::vector<std::vector<std::string>> ans;
//         for (const auto &t : leafSymbolMap.at(state)) {
//             std::string result = "(";
//             bool start = false;
//             for (unsigned i=0; i<t.complex.size()-1; i++) {
//                 if (i == 0 && t.complex.at(0) == 0 && t.complex.at(1) == 0 && t.complex.at(2) == 0 && t.complex.at(3) == 0 || t.complex.at(i) != 0) {
//                     if (start) result += " + ";
//                     result += t.complex.at(i).str();
//                     if (i >= 1) result += " * ei2pi(" + std::to_string(i) + "/8)";
//                     start = true;
//                 }
//             }
//             result += ") / sqrt2 ^ " + t.complex.at(4).str();
//             ans.push_back({result});
//         }
//         return ans;
//     }
//     std::vector<std::vector<std::string>> ans;
//     for (const auto &out_ins : transitions.at({qubit})) {
//         if (out_ins.first == state) {
//             for (const auto &in : out_ins.second) {
//                 auto v1 = get_all_languages_under_the_state_at_this_level(leafSymbolMap, qubit + 1, in.at(0));
//                 auto v2 = get_all_languages_under_the_state_at_this_level(leafSymbolMap, qubit + 1, in.at(1));
//                 for (const auto &s1 : v1) {
//                     for (const auto &s2 : v2) {
//                         auto v = s1;
//                         v.insert(v.end(), s2.begin(), s2.end());
//                         ans.push_back(v);
//                     }
//                 }
//             }
//         }
//     }
//     return ans;
// }

template <typename Symbol>
void AUTOQ::Automata<Symbol>::print_language(const std::string &prompt) const {
    std::cout << prompt;
    for (const auto &s : finalStates) {
        auto v = get_all_languages_under_the_state_at_this_level<Symbol>(this, 1, s);
        for (const auto &s : v) {
            std::map<std::string, int> count;
            for (unsigned i=0; i<s.size(); i++)
                count[s[i]]++;
            auto ptr = std::max_element(count.begin(), count.end(), [](const auto &x, const auto &y) {
                return x.second < y.second;
            });
            for (unsigned i=0; i<s.size(); i++) {
                if (s[i] != (ptr->first))
                    std::cout << boost::dynamic_bitset(qubitNum, i) << ":" << s[i] << " | ";
            }
            std::cout << "*:" << (ptr->first) << std::endl;
        }
    }
}

// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Predicate>;
