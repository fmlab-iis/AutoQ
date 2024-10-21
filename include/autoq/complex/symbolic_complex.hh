#ifndef _AUTOQ_SYMBOLICCOMPLEX_HH_
#define _AUTOQ_SYMBOLICCOMPLEX_HH_

#include "autoq/util/convert.hh"
#include "autoq/complex/complex.hh"
#include <boost/multiprecision/cpp_int.hpp>

typedef boost::rational<boost::multiprecision::cpp_int> rational;

namespace AUTOQ {
	namespace Complex {
        struct SymbolicComplex;
        struct Term;
	}
}

struct AUTOQ::Complex::Term : std::map<std::string, boost::multiprecision::cpp_int> {
    Term operator+(Term o) const {
        for (const auto &kv : *this) {
            o[kv.first] += kv.second;
            // if (o[kv.first] == 0)
            //     o.erase(kv.first);
        }
        return o;
    }
    std::string expand() const { // can only be used in (* ...)
        if (empty()) return "1";
        std::string result = size() >= 2 ? "(+" : "";
        bool isFirst = true;
        for (const auto &kv : *this) {
            const auto &s = kv.first;
            auto v = kv.second;
            assert(v != 0);
            if (v == 1)
                result += std::string((!isFirst) ? " " : "") + s;
            else
                result += std::string((!isFirst) ? " " : "") + "(* " + s + " " + v.str() + ")";
            isFirst = false;
        }
        result += size() >= 2 ? ")" : "";
        return result;
    }
    friend std::ostream& operator<<(std::ostream& os, const Term& obj) {
        os << obj.expand();
        return os;
    }
};
struct AUTOQ::Complex::SymbolicComplex : std::map<Term, Complex> {
    static SymbolicComplex MySymbolicComplexConstructor(int i) {
        return MySymbolicComplexConstructor(Complex(i));
    }
    static SymbolicComplex MySymbolicComplexConstructor(const Complex &c) {
        if (c.isZero()) return {}; // IMPORTANT: keep the keys nonzero to simplify the structure very much!
        SymbolicComplex result;
        result[Term()] = c;
        return result;
    }
    static SymbolicComplex MySymbolicComplexConstructor(const std::string &name) {
        std::set<std::string> vars;
        return MySymbolicComplexConstructor(name, vars);
    }
    static SymbolicComplex MySymbolicComplexConstructor(const std::string &name, std::set<std::string> &vars) {
        vars.insert(name + "R");
        vars.insert(name + "I");
        SymbolicComplex result;
        Term key; key[name + "R"] = 1;
        result[key] = Complex::One();
        key.clear(); key[name + "I"] = 1;
        result[key] = Complex::Angle(rational(2, 8));
        return result;
    }
    SymbolicComplex operator+(SymbolicComplex o) const {
        for (const auto &kv : *this) {
            o[kv.first] = o[kv.first] + kv.second;
            if (o[kv.first].isZero())
                o.erase(kv.first);
        }
        return o;
    }
    SymbolicComplex& operator+=(const SymbolicComplex &o) { *this = *this + o; return *this; }
    SymbolicComplex operator-(const SymbolicComplex &o) const {
        auto result = *this;
        for (const auto &kv : o) {
            result[kv.first] = result[kv.first] - kv.second;
            if (result[kv.first].isZero())
                result.erase(kv.first);
        }
        return result;
    }
    SymbolicComplex operator*(const SymbolicComplex &o) const {
        AUTOQ::Complex::SymbolicComplex result;
        std::set<Term> keys;
        for (const auto &kv1 : *this) {
            for (const auto &kv2 : o) {
                auto key = kv1.first + kv2.first;
                keys.insert(key);
                result[key] = result[key] + kv1.second * kv2.second;
            }
        }
        for (const auto &key : keys) {
            if (result.at(key).isZero())
                result.erase(key);
        }
        return result;
    }
    SymbolicComplex operator/(const Complex &o) const {
        AUTOQ::Complex::SymbolicComplex result;
        for (const auto &kv : *this) {
            result[kv.first] = kv.second / o;
        }
        return result;
    }
    SymbolicComplex operator*(int c) const {
        SymbolicComplex result;
        if (c != 0) {
            for (const auto &kv : *this) {
                result[kv.first] = kv.second * c;
            }
        }
        return result;
    }
    friend std::ostream& operator<<(std::ostream& os, const SymbolicComplex& obj) {
        bool isFirst = true;
        for (const auto &tc : static_cast<std::map<Term, Complex>>(obj)) {
            if (tc.second.isZero()) continue;
            if (!isFirst) os << " + ";
            if (tc.second != Complex(1) || tc.first.empty())
                os << tc.second;
            if (!tc.first.empty()) {
                if (tc.second != Complex(1))
                    os << " * ";
                os << tc.first;
            }
            isFirst = false;
        }
        if (obj.empty()) os << "0";
        return os;
    }
    std::string realToSMT() const {
        if (empty()) return "0";
        bool isFirst = true;
        std::string result = size() >= 2 ? "(+" : "";
        for (const auto &kv : *this) {
            auto k = kv.first;
            auto v = kv.second;
            if (v.realToSMT() == "1")
                result += std::string((!isFirst) ? " " : "") + k.expand();
            else
                result += std::string((!isFirst) ? " " : "") + "(* " + k.expand() + " " + v.realToSMT() + ")";
            isFirst = false;
        }
        result += size() >= 2 ? ")" : "";
        return result;
    }
    SymbolicComplex real() const {
        SymbolicComplex result;
        for (const auto &kv : *this) {
            auto k = kv.first;
            auto v = kv.second.real();
            if (v.isZero()) continue;
            result[k] = v;
        }
        return result;
    }
    std::string imagToSMT() const {
        if (empty()) return "0";
        bool isFirst = true;
        std::string result = size() >= 2 ? "(+" : "";
        for (const auto &kv : *this) {
            auto k = kv.first;
            auto v = kv.second;
            if (v.imagToSMT() == "1")
                result += std::string((!isFirst) ? " " : "") + k.expand();
            else
                result += std::string((!isFirst) ? " " : "") + "(* " + k.expand() + " " + v.imagToSMT() + ")";
            isFirst = false;
        }
        result += size() >= 2 ? ")" : "";
        return result;
    }
    SymbolicComplex imag() const {
        SymbolicComplex result;
        for (const auto &kv : *this) {
            auto k = kv.first;
            auto v = kv.second.imag();
            if (v.isZero()) continue;
            result[k] = v;
        }
        return result;
    }
    void fraction_simplification() {
        for (auto &kv : *this) {
            kv.second.fraction_simplification();
        }
    }
    bool isConst() const {
        return empty() || (size() == 1 && begin()->first.empty());
    }
    rational to_rational() const {
        assert(isConst());
        if (empty()) return 0;
        return begin()->second.to_rational();
    }
    boost::multiprecision::cpp_int max_k() const {
        boost::multiprecision::cpp_int k = INT_MIN;
        for (auto kv : *this) {
            if (k < kv.second.k())
                k = kv.second.k();
        }
        return k;
    }
    void adjust_k_and_discard(boost::multiprecision::cpp_int k) {
        fraction_simplification();
        for (auto &kv : *this) {
            auto &c = kv.second;
            while (c.k() < k)
                c.increase_k();
            c.k() = 0;
        }
    }
    std::set<std::string> vars() const {
        std::set<std::string> result;
        for (const auto &kv : *this) {
            for (const auto &kv2 : kv.first) {
                result.insert(kv2.first);
            }
        }
        return result;
    }
};

#endif
