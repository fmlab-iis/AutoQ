#ifndef _AUTOQ_SYMBOLIC_HH_
#define _AUTOQ_SYMBOLIC_HH_

#include <autoq/util/convert.hh>
#include <autoq/complex/symbolic_complex.hh>
#include <boost/multiprecision/cpp_int.hpp>

namespace AUTOQ {
	namespace Symbol {
        struct Symbolic;
	}
}

struct AUTOQ::Symbol::Symbolic {
private:
    bool internal;
public:
    AUTOQ::Complex::SymbolicComplex complex;

    // Notice that if we do not use is_convertible_v, type int will not be accepted in this case.
    template <typename T, typename = std::enable_if_t<std::is_convertible<T, boost::multiprecision::cpp_int>::value>>
        Symbolic(T qubit) : internal(true), complex({{Complex::Complex::One(), AUTOQ::Complex::linear_combination({{"1", qubit}})}}) {}
    Symbolic(const std::map<Complex::Complex, AUTOQ::Complex::linear_combination> &c) : internal(false), complex(c) {}
    Symbolic(const AUTOQ::Complex::SymbolicComplex &c) : internal(false), complex(c) {}
    Symbolic() : internal(false), complex() {} // prevent the compiler from complaining about the lack of default constructor
    // Symbolic() : internal(false), complex({{Complex::Complex::Zero(), AUTOQ::Complex::linear_combination({{"1", 1}})}}) {} // prevent the compiler from complaining about the lack of default constructor
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
    Symbolic operator+(const Symbolic &o) const {
        return Symbolic(complex + o.complex);
    }
    Symbolic operator-(const Symbolic &o) const {
        return Symbolic(complex - o.complex);
    }
    Symbolic operator*(const Symbolic &o) const {
        return Symbolic(complex * o.complex);
    }
    Symbolic operator*(int c) const {
        return complex * c;
    }
    void fraction_simplification() {
        complex.fraction_simplification();
    }
    void omega_multiplication(int rotation=1) {
        if (rotation > 0) {
            AUTOQ::Complex::SymbolicComplex complex2;
            for (const auto &kv : complex) {
                auto k = kv.first;
                auto v = kv.second;
                complex2[k.counterclockwise(boost::rational<boost::multiprecision::cpp_int>(rotation, 8))] = v;
            }
            complex = complex2;
        }
        if (rotation < 0) {
            AUTOQ::Complex::SymbolicComplex complex2;
            for (const auto &kv : complex) {
                auto k = kv.first;
                auto v = kv.second;
                complex2[k.clockwise(boost::rational<boost::multiprecision::cpp_int>(rotation, 8))] = v;
            }
            complex = complex2;
        }
    }
    void divide_by_the_square_root_of_two() {
        AUTOQ::Complex::SymbolicComplex complex2;
        for (const auto &kv : complex) {
            auto k = kv.first;
            auto v = kv.second;
            complex2[k.divide_by_the_square_root_of_two()] = v;
        }
        complex = complex2;
    }
    void negate() {
        AUTOQ::Complex::SymbolicComplex complex2;
        for (const auto &kv : complex) {
            auto k = kv.first;
            auto v = kv.second;
            complex2[k * (-1)] = v;
        }
        complex = complex2;
    }
    void degree45cw() {
        AUTOQ::Complex::SymbolicComplex complex2;
        for (const auto &kv : complex) {
            auto k = kv.first;
            auto v = kv.second;
            complex2[k.clockwise(boost::rational<boost::multiprecision::cpp_int>(1, 8))] = v;
        }
        complex = complex2;
    }
    void degree90cw() {
        AUTOQ::Complex::SymbolicComplex complex2;
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