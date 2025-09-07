#ifndef _AUTOQ_CONSTRAINEDCOMPLEX_HH_
#define _AUTOQ_CONSTRAINEDCOMPLEX_HH_

#include "autoq/util/convert.hh"
#include "autoq/complex/complex.hh"
#include <boost/multiprecision/cpp_int.hpp>

typedef boost::rational<boost::multiprecision::cpp_int> rational;

namespace AUTOQ {
	namespace Complex {
        struct ConstrainedComplex;
	}
}

struct AUTOQ::Complex::ConstrainedComplex : std::map<int, std::tuple<std::string, std::vector<bool>, std::vector<bool>>> {
    ConstrainedComplex() {}
    ConstrainedComplex(int termId,
                       std::string coefficient,
                       std::vector<bool> global_constraints,
                       std::vector<bool> local_constraints) {
        (*this)[termId] = std::make_tuple(coefficient, global_constraints, local_constraints);
    }
    ConstrainedComplex operator+(ConstrainedComplex o) const {
        for (const auto &[k, v] : *this) {
            if (o.find(k) != o.end()) {
                THROW_AUTOQ_ERROR("Term ID " + std::to_string(k) + " already exists in ConstrainedComplex!");
            }
            o[k] = v;
        }
        return o;
    }
    ConstrainedComplex& operator+=(const ConstrainedComplex &o) { *this = *this + o; return *this; }
    ConstrainedComplex operator*(const ConstrainedComplex &o) const {
        AUTOQ::Complex::ConstrainedComplex result;

        if (this->size() < o.size()) {
            for (const auto &[k, v] : *this) {
                auto it = o.find(k);
                if (it != o.end()) { // we only merge common terms (keys)
                    std::tuple<std::string, std::vector<bool>, std::vector<bool>> obj;
                    const auto &w = it->second;
                    if (std::get<0>(v) != std::get<0>(w)) {
                        THROW_AUTOQ_ERROR("One term can only have one coefficient!");
                    } else {
                        std::get<0>(obj) = std::get<0>(v);
                    }
                    if (std::get<1>(v).size() != std::get<1>(w).size()) {
                        THROW_AUTOQ_ERROR("All terms should have the same number of global constraints!");
                    } else {
                        const auto &a = std::get<1>(v);
                        const auto &b = std::get<1>(w);
                        auto &c = std::get<1>(obj);
                        c.resize(a.size());
                        for (size_t i = 0; i < a.size(); ++i) {
                            c[i] = a[i] || b[i]; // merge global constraints
                        }
                    }
                    if (std::get<2>(v).size() != std::get<2>(w).size()) {
                        THROW_AUTOQ_ERROR("The same terms should have the same number of local constraints!");
                    } else {
                        const auto &a = std::get<2>(v);
                        const auto &b = std::get<2>(w);
                        auto &c = std::get<2>(obj);
                        c.resize(a.size());
                        for (size_t i = 0; i < a.size(); ++i) {
                            c[i] = a[i] || b[i]; // merge global constraints
                        }
                    }
                    result[k] = obj;
                }
            }
        } else {
            for (const auto &[k, v] : o) {
                auto it = this->find(k);
                if (it != this->end()) { // we only merge common terms (keys)
                    std::tuple<std::string, std::vector<bool>, std::vector<bool>> obj;
                    const auto &w = it->second;
                    if (std::get<0>(v) != std::get<0>(w)) {
                        THROW_AUTOQ_ERROR("One term can only have one coefficient!");
                    } else {
                        std::get<0>(obj) = std::get<0>(v);
                    }
                    if (std::get<1>(v).size() != std::get<1>(w).size()) {
                        THROW_AUTOQ_ERROR("All terms should have the same number of global constraints!");
                    } else {
                        const auto &a = std::get<1>(v);
                        const auto &b = std::get<1>(w);
                        auto &c = std::get<1>(obj);
                        c.resize(a.size());
                        for (size_t i = 0; i < a.size(); ++i) {
                            c[i] = a[i] || b[i]; // merge global constraints
                        }
                    }
                    if (std::get<2>(v).size() != std::get<2>(w).size()) {
                        THROW_AUTOQ_ERROR("The same terms should have the same number of local constraints!");
                    } else {
                        const auto &a = std::get<2>(v);
                        const auto &b = std::get<2>(w);
                        auto &c = std::get<2>(obj);
                        c.resize(a.size());
                        for (size_t i = 0; i < a.size(); ++i) {
                            c[i] = a[i] || b[i]; // merge global constraints
                        }
                    }
                    result[k] = obj;
                }
            }
        }
        return result;
    }
    friend std::ostream& operator<<(std::ostream& os, const ConstrainedComplex& obj) {
        for (const auto &[termId, coe] : obj) {
            os << "(" << termId << ":";
            os << std::get<0>(coe);
            for (const auto &vec : {std::get<1>(coe), std::get<2>(coe)}) { // global constraints, local constraints
                os << "[";
                for (const auto &b : vec) {
                    os << (b ? "T" : "F");
                }
                os << "]";
            }
            os << ")";
        }
        return os;
    }
    void fraction_simplification() {
        auto result = AUTOQ::Complex::ConstrainedComplex();
        for (const auto &[k, v] : *this) {
            if (std::all_of(std::get<1>(v).begin(), std::get<1>(v).end(), [](bool b) { return b; })
             && std::all_of(std::get<2>(v).begin(), std::get<2>(v).end(), [](bool b) { return b; })) {
                result[k] = std::make_tuple(std::get<0>(v), std::vector<bool>(), std::vector<bool>());
            }
        }
        *this = result;
    }
};

#endif
