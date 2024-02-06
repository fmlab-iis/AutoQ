#ifndef _AUTOQ_SYMBOLICCOMPLEX_HH_
#define _AUTOQ_SYMBOLICCOMPLEX_HH_

#include <autoq/util/convert.hh>
#include <autoq/complex/complex.hh>
#include <boost/multiprecision/cpp_int.hpp>

namespace AUTOQ {
	namespace Complex {
        struct linear_combination;
        struct SymbolicComplex;
	}
}

// Symbolic symbol
typedef std::map<std::string, boost::multiprecision::cpp_int> stdmapstdstringboostmultiprecisioncpp_int;
struct AUTOQ::Complex::linear_combination : std::map<std::string, boost::multiprecision::cpp_int> {
    using stdmapstdstringboostmultiprecisioncpp_int::stdmapstdstringboostmultiprecisioncpp_int;
    bool trueMustBeZero() const {
        for (const auto &kv : *this) {
            if (kv.second != 0)
                return false;
        }
        return true;
    }
    linear_combination operator+(linear_combination b) const {
        for (const auto &kv : *this) {
            auto k = kv.first;
            auto v = kv.second;
            b[k] += v;
            if (b[k] == 0)
                b.erase(k);
        }
        return b;
    }
    linear_combination operator-(const linear_combination &b) const {
        auto a = *this; // copy!
        for (const auto &kv : b) {
            auto k = kv.first;
            auto v = kv.second;
            a[k] -= v;
            if (a[k] == 0)
                a.erase(k);
        }
        return a;
    }
    linear_combination operator*(int c) const {
        linear_combination result;
        for (const auto &kv : *this) {
            if (c != 0)
                result[kv.first] = kv.second * c;
        }
        return result;
    }
    linear_combination operator*(const linear_combination &b) const {
        linear_combination ans;
        for (const auto &kv1 : *this) {
            for (const auto &kv2 : b) {
                if (kv1.first == "1") {
                    ans[kv2.first] += kv1.second * kv2.second;
                } else if (kv2.first == "1") {
                    ans[kv1.first] += kv1.second * kv2.second;
                } else if (kv1.first < kv2.first) {
                    ans["(* " + kv1.first + " " + kv2.first + ")"] += kv1.second * kv2.second;
                } else {
                    ans["(* " + kv2.first + " " + kv1.first + ")"] += kv1.second * kv2.second;
                }
            }
        }
        return ans;
    }
    friend std::ostream& operator<<(std::ostream& os, const linear_combination& obj) {
        // os << AUTOQ::Util::Convert::ToString(static_cast<stdmapstdstringboostmultiprecisioncpp_int>(obj));
        if (obj.empty()) {
            os << "0";
            return os;
        }
        for (auto kv = obj.begin(); kv != obj.end(); ++kv) {
            if (kv->first == "1")
                os << kv->second;
            else {
                if (kv->second != 1)
                    os << kv->second;
                os << kv->first;
            }
            if (std::next(kv) != obj.end())
                os << ' ';
        }
        return os;
    }
    std::string toSMT() const { // std::map<std::string, boost::multiprecision::cpp_int>
        if (empty()) return "0";
        std::string result = "(+";
        for (const auto &kv : *this) {
            auto k = kv.first;
            auto v = kv.second;
            result += " (* " + k + " " + v.str() + ")";
        }
        result += ")";
        return result;
    }
    boost::multiprecision::cpp_int toInt() const {
        return at("1");
    }
};

struct AUTOQ::Complex::SymbolicComplex : std::map<Complex, AUTOQ::Complex::linear_combination> {
    std::string smt_real;

    static SymbolicComplex MySymbolicComplexConstructor(const Complex &c) {
        if (c.isZero()) return {}; // IMPORTANT: keep the keys nonzero to simplify the structure very much!
        SymbolicComplex result;
        result[c] = {{ "1", 1 }};
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
        result[Complex::One()] = {{name + "R", 1}};
        result[Complex::Angle(rational(2, 8))] = {{name + "I", 1}};
        return result;
    }
    SymbolicComplex operator+(const SymbolicComplex &o) const {
        if (!smt_real.empty() || !o.smt_real.empty()) {
            if (smt_real.empty() || o.smt_real.empty()) {
                throw std::runtime_error(AUTOQ_LOG_PREFIX + "The two operand types are not consistent!");
            }
            SymbolicComplex result;
            result.smt_real = "(+ " + smt_real + " " + o.smt_real + ")";
            return result;
        }
        //
        auto complex2 = *this;
        for (const auto &kv : o) {
            complex2[kv.first] = complex2[kv.first] + kv.second;
            if (complex2[kv.first].trueMustBeZero())
                complex2.erase(kv.first);
        }
        return complex2;
    }
    SymbolicComplex operator-(const SymbolicComplex &o) const {
        if (!smt_real.empty() || !o.smt_real.empty()) {
            if (smt_real.empty() || o.smt_real.empty()) {
                throw std::runtime_error(AUTOQ_LOG_PREFIX + "The two operand types are not consistent!");
            }
            SymbolicComplex result;
            result.smt_real = "(- " + smt_real + " " + o.smt_real + ")";
            return result;
        }
        //
        auto complex2 = *this;
        for (const auto &kv : o) {
            complex2[kv.first] = complex2[kv.first] - kv.second;
            if (complex2[kv.first].trueMustBeZero())
                complex2.erase(kv.first);
        }
        return complex2;
    }
    SymbolicComplex operator*(const SymbolicComplex &o) const {
        if (!smt_real.empty() || !o.smt_real.empty()) {
            if (smt_real.empty() || o.smt_real.empty()) {
                throw std::runtime_error(AUTOQ_LOG_PREFIX + "The two operand types are not consistent!");
            }
            SymbolicComplex result;
            result.smt_real = "(* " + smt_real + " " + o.smt_real + ")";
            return result;
        }
        //
        AUTOQ::Complex::SymbolicComplex complex2;
        for (const auto &kv1 : *this) {
            for (const auto &kv2 : o) {
                complex2[kv1.first * kv2.first] = complex2[kv1.first * kv2.first] + kv1.second * kv2.second;
            }
        }
        AUTOQ::Complex::SymbolicComplex complex1;
        for (const auto &kv : complex2) {
            auto k = kv.first;
            auto v = kv.second;
            if (k.isZero() || v.trueMustBeZero()) continue;
            complex1[k] = v;
        }
        return complex1;
        /* This operator also explains why our number is a mapping
        from "complex" to "linear combination" instead of a mapping
        from "variable" to "complex". If we adopt the latter mapping,
        the multiplication of two variables cannot be a "variable" anymore. */
    }
    SymbolicComplex operator/(const Complex &o) const {
        AUTOQ::Complex::SymbolicComplex complex2;
        for (const auto &kv : *this) {
            complex2[kv.first / o] = kv.second;
        }
        return complex2;
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
        os << AUTOQ::Util::Convert::ToString(static_cast<std::map<Complex, AUTOQ::Complex::linear_combination>>(obj));
        return os;
    }
    std::string realToSMT() const { // std::map<Complex, AUTOQ::Complex::linear_combination> complex;
        if (!smt_real.empty()) return smt_real;
        //
        if (empty()) return "0";
        std::string result = "(+";
        for (const auto &kv : *this) {
            auto k = kv.first;
            auto v = kv.second;
            result += " (* " + k.realToSMT() + " " + v.toSMT() + ")";
        }
        result += ")";
        return result;
    }
    SymbolicComplex real() const {
        if (!smt_real.empty()) return *this;
        //
        SymbolicComplex result, result2;
        for (const auto &kv : *this) {
            auto k = kv.first.real();
            auto v = kv.second;
            if (k.isZero()) continue;
            result2[k] = result2[k] + v;
        }
        for (const auto &kv : result2) {
            auto k = kv.first;
            auto v = kv.second;
            if (result2[k].trueMustBeZero()) continue;
            result[k] = v;
        }
        return result;
    }
    std::string imagToSMT() const { // std::map<Complex, AUTOQ::Complex::linear_combination> complex;
        if (!smt_real.empty() || empty()) return "0";
        //
        std::string result = "(+";
        for (const auto &kv : *this) {
            auto k = kv.first;
            auto v = kv.second;
            result += " (* " + k.imagToSMT() + " " + v.toSMT() + ")";
        }
        result += ")";
        return result;
    }
    SymbolicComplex imag() const {
        if (!smt_real.empty()) {
            SymbolicComplex result;
            result.smt_real = "0";
            return result;
        }
        //
        SymbolicComplex result, result2;
        for (const auto &kv : *this) {
            auto k = kv.first.imag();
            auto v = kv.second;
            if (k.isZero()) continue;
            result2[k] = result2[k] + v;
        }
        for (const auto &kv : result2) {
            auto k = kv.first;
            auto v = kv.second;
            if (result2[k].trueMustBeZero()) continue;
            result[k] = v;
        }
        return result;
    }
    void fraction_simplification() {
        SymbolicComplex complex2;
        for (const auto &kv : *this) {
            auto k = kv.first;
            auto v = kv.second;
            if (k.isZero() || v.trueMustBeZero()) continue;
            k.fraction_simplification();
            #ifdef COMPLEX_FiveTuple
            if (k.at(0) < 0) {
                k = k * (-1);
                complex2[k] = complex2[k] - v;
            } else
            #endif
                complex2[k] = complex2[k] + v;
        }
        #ifdef COMPLEX_FiveTuple
        *this = complex2;
        complex2.clear();
        for (const auto &kv : *this) {
            auto k = kv.first;
            auto v = kv.second;
            while (k.at(4) >= 2) {
                int denominator = 2;
                for (const auto &vc : v) {
                    auto coe = vc.second;
                    if (coe % 2 != 0)
                        denominator = 1;
                }
                if (denominator == 1) break;
                k.at(4) = k.at(4) - 2;
                for (auto &vc : v) {
                    vc.second /= 2;
                }
            }
            complex2[k] = complex2[k] + v;
        }
        #endif
        *this = complex2;
    }
    rational to_rational() const {
        return this->begin()->first.to_rational();
    }
};

#endif
