#ifndef _AUTOQ_SYMBOLIC_HH_
#define _AUTOQ_SYMBOLIC_HH_

#include <vector>
#include <autoq/util/convert.hh>
#include <boost/multiprecision/cpp_int.hpp>

namespace AUTOQ
{
	namespace Symbol
	{
        struct linear_combination;
        struct Symbolic;
        struct SymbolicComplex;
	}
}

// Symbolic symbol
typedef std::map<std::string, boost::multiprecision::cpp_int> stdmapstdstringboostmultiprecisioncpp_int;
struct AUTOQ::Symbol::linear_combination : std::map<std::string, boost::multiprecision::cpp_int> {
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
        }
        return b;
    }
    linear_combination operator-(const linear_combination &b) const {
        auto a = *this; // copy!
        for (const auto &kv : b) {
            auto k = kv.first;
            auto v = kv.second;
            a[k] -= v;
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
                    ans[kv1.first + "*" + kv2.first] += kv1.second * kv2.second;
                } else {
                    ans[kv2.first + "*" + kv1.first] += kv1.second * kv2.second;
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
};

struct AUTOQ::Symbol::SymbolicComplex : std::map<Complex::Complex, AUTOQ::Symbol::linear_combination> {
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
        os << AUTOQ::Util::Convert::ToString(static_cast<std::map<Complex::Complex, AUTOQ::Symbol::linear_combination>>(obj));
        return os;
    }
    std::string realToSMT() const { // std::map<Complex::Complex, AUTOQ::Symbol::linear_combination> complex;
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
    std::string imagToSMT() const { // std::map<Complex::Complex, AUTOQ::Symbol::linear_combination> complex;
        if (empty()) return "0";
        std::string result = "(+";
        for (const auto &kv : *this) {
            auto k = kv.first;
            auto v = kv.second;
            result += " (* " + k.imagToSMT() + " " + v.toSMT() + ")";
        }
        result += ")";
        return result;
    }
};
struct AUTOQ::Symbol::Symbolic {
private:
    bool internal;
public:
    AUTOQ::Symbol::SymbolicComplex complex;

    // Notice that if we do not use is_convertible_v, type int will not be accepted in this case.
    template <typename T, typename = std::enable_if_t<std::is_convertible<T, boost::multiprecision::cpp_int>::value>>
        Symbolic(T qubit) : internal(true), complex({{Complex::Complex::One(), AUTOQ::Symbol::linear_combination({{"1", qubit}})}}) {}
    Symbolic(const std::map<Complex::Complex, AUTOQ::Symbol::linear_combination> &c) : internal(false), complex(c) {}
    Symbolic() : internal(false), complex() {} // prevent the compiler from complaining about the lack of default constructor
    // Symbolic() : internal(false), complex({{Complex::Complex::Zero(), AUTOQ::Symbol::linear_combination({{"1", 1}})}}) {} // prevent the compiler from complaining about the lack of default constructor
    bool is_internal() const { return internal; }
    bool is_leaf() const { return !internal; }
    boost::multiprecision::cpp_int qubit() const {
        assert(internal);
        // assert(complex.imag() == 0);
        return complex.at(Complex::Complex::One()).at("1");
    }
    void back_to_zero() { complex.clear(); }
    friend std::ostream& operator<<(std::ostream& os, const Symbolic& obj) {
        os << AUTOQ::Util::Convert::ToString(obj.complex);
        return os;
    }
    bool operator==(const Symbolic &o) const { return internal == o.internal && complex == o.complex; }
    bool operator<(const Symbolic &o) const {
        if (internal && !o.internal) return true;
        if (o.internal && !internal) return false;
        return complex < o.complex;
    }
    Symbolic operator+(const Symbolic &o) const { return binary_operation(o, true); }
    Symbolic operator-(const Symbolic &o) const { return binary_operation(o, false); }
    Symbolic binary_operation(Symbolic o, bool add) const {
        auto complex2 = complex;
        for (const auto &kv2 : o.complex) {
            if (add)
                complex2[kv2.first] = complex2[kv2.first] + kv2.second;
            else
                complex2[kv2.first] = complex2[kv2.first] - kv2.second;
        }
        return Symbolic(complex2);
    }
    Symbolic operator*(const Symbolic &o) const {
        SymbolicComplex complex2;
        for (const auto &kv1 : complex) {
            for (const auto &kv2 : o.complex) {
                complex2[kv1.first * kv2.first] = kv1.second * kv2.second;
            }
        }
        return Symbolic(complex2);
        /* This operator also explains why our number is a mapping
        from "complex" to "linear combination" instead of a mapping
        from "variable" to "complex". If we adopt the latter mapping,
        the multiplication of two variables cannot be a "variable" anymore. */
    }
    Symbolic operator*(int c) const {
        return complex * c;
    }
    void fraction_simplification() {
        SymbolicComplex complex2;
        for (const auto &kv : complex) {
            auto k = kv.first;
            auto v = kv.second;
            if (k.isZero() || v.trueMustBeZero()) continue;
            complex2[k.fraction_simplification()] = complex2[k.fraction_simplification()] + v;
        }
        complex = complex2;
    }
    void omega_multiplication(int rotation=1) {
        if (rotation > 0) {
            SymbolicComplex complex2;
            for (const auto &kv : complex) {
                auto k = kv.first;
                auto v = kv.second;
                complex2[k.counterclockwise(boost::rational<boost::multiprecision::cpp_int>(rotation, 8))] = v;
            }
            complex = complex2;
        }
        if (rotation < 0) {
            SymbolicComplex complex2;
            for (const auto &kv : complex) {
                auto k = kv.first;
                auto v = kv.second;
                complex2[k.clockwise(boost::rational<boost::multiprecision::cpp_int>(rotation, 8))] = v;
            }
            complex = complex2;
        }
    }
    void divide_by_the_square_root_of_two() {
        SymbolicComplex complex2;
        for (const auto &kv : complex) {
            auto k = kv.first;
            auto v = kv.second;
            complex2[k.divide_by_the_square_root_of_two()] = v;
        }
        complex = complex2;
    }
    void negate() {
        SymbolicComplex complex2;
        for (const auto &kv : complex) {
            auto k = kv.first;
            auto v = kv.second;
            complex2[k * (-1)] = v;
        }
        complex = complex2;
    }
    void degree45cw() {
        SymbolicComplex complex2;
        for (const auto &kv : complex) {
            auto k = kv.first;
            auto v = kv.second;
            complex2[k.clockwise(boost::rational<boost::multiprecision::cpp_int>(1, 8))] = v;
        }
        complex = complex2;
    }
    void degree90cw() {
        SymbolicComplex complex2;
        for (const auto &kv : complex) {
            auto k = kv.first;
            auto v = kv.second;
            complex2[k.clockwise(boost::rational<boost::multiprecision::cpp_int>(1, 4))] = v;
        }
        complex = complex2;
    }
};

namespace boost {
    template <> struct hash<AUTOQ::Symbol::Symbolic> {
        size_t operator()(const AUTOQ::Symbol::Symbolic& obj) const {
            std::size_t seed = 0;
            boost::hash_combine(seed, obj.is_internal());
            boost::hash_combine(seed, obj.complex);
            return seed;
        }
    };
}

#endif