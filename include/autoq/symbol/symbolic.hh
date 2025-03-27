#ifndef _AUTOQ_SYMBOLIC_HH_
#define _AUTOQ_SYMBOLIC_HH_

#include "autoq/error.hh"
#include "autoq/util/convert.hh"
#include "autoq/complex/symbolic_complex.hh"
#include <boost/multiprecision/cpp_int.hpp>
#include <boost/functional/hash.hpp>

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
    Symbolic(T qubit) : internal(true), complex(AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor(qubit)) {}
    Symbolic(const std::map<AUTOQ::Complex::Term, AUTOQ::Complex::Complex> &c) : internal(false), complex(Complex::SymbolicComplex::MySymbolicComplexConstructor(c)) {}
    Symbolic(const AUTOQ::Complex::SymbolicComplex &c) : internal(false), complex(c) {}
    Symbolic() : internal(false), complex() {} // prevent the compiler from complaining about the lack of default constructor
    // Symbolic() : internal(false), complex({{Complex::Complex::Zero(), AUTOQ::Complex::linear_combination({{"1", 1}})}}) {} // prevent the compiler from complaining about the lack of default constructor
    bool is_internal() const { return internal; }
    bool is_leaf() const { return !internal; }
    boost::multiprecision::cpp_int qubit() const {
        if (!internal) {
            THROW_AUTOQ_ERROR("Leaf symbols do not have qubit().");
        }
        return complex.begin()->second.toInt();
    }
    void back_to_zero() { complex.clear(); }
    std::string str() const {
        std::stringstream ss;
        ss << *this; // simply employ the following operator<<
        return ss.str();
    }
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
    Symbolic counterclockwise(const boost::rational<boost::multiprecision::cpp_int> &theta) {
        for (auto &kv : complex)
            kv.second.counterclockwise(theta);
        return *this;
    }
    Symbolic omega_multiplication(int rotation=1) {
        if (rotation > 0) {
            for (auto &kv : complex)
                kv.second.counterclockwise(boost::rational<boost::multiprecision::cpp_int>(rotation, 8));
        }
        if (rotation < 0) {
            for (auto &kv : complex)
                kv.second.clockwise(boost::rational<boost::multiprecision::cpp_int>(-rotation, 8));
        }
        return *this;
    }
    Symbolic divide_by_the_square_root_of_two() {
        for (auto &kv : complex) {
            kv.second.divide_by_the_square_root_of_two();
        }
        return *this;
    }
    void negate() {
        for (auto &kv : complex) {
            kv.second = kv.second * -1;
        }
    }
    void degree45cw() {
        omega_multiplication(-1);
    }
    void degree90cw() {
        omega_multiplication(-2);
    }
    Symbolic multiply_cos(const boost::rational<boost::multiprecision::cpp_int> &theta) {
        for (auto &kv : complex)
            kv.second.multiply_cos(theta);
        return *this;
    }
    Symbolic multiply_isin(const boost::rational<boost::multiprecision::cpp_int> &theta) {
        for (auto &kv : complex)
            kv.second.multiply_isin(theta);
        return *this;
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
