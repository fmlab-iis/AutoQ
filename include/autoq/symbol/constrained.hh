#ifndef _AUTOQ_CONSTRAINED_HH_
#define _AUTOQ_CONSTRAINED_HH_

#include <vector>
#include "autoq/util/convert.hh"
#include "autoq/complex/complex.hh"
#include "autoq/complex/constrained_complex.hh"
#include <boost/multiprecision/cpp_int.hpp>
#include <boost/functional/hash.hpp>

namespace AUTOQ
{
	namespace Symbol
	{
        struct Constrained;
	}
}

// Constrained symbol
struct AUTOQ::Symbol::Constrained {
public:
    int qubiT = 0;
    Complex::ConstrainedComplex complex;

    // Notice that if we do not use is_convertible_v, type int will not be accepted in this case.
    template <typename T, typename = std::enable_if_t<std::is_convertible<T, boost::multiprecision::cpp_int>::value>>
        Constrained(T qubit) : qubiT(qubit), complex() {}
    Constrained(const Complex::ConstrainedComplex &c) : qubiT(0), complex(c) {}
    Constrained() : qubiT(), complex() {} // prevent the compiler from complaining about the lack of default constructor
    bool is_internal() const { return qubiT != 0; }
    bool is_leaf() const { return qubiT == 0; }
    boost::multiprecision::cpp_int qubit() const {
        return qubiT;
    }
    void back_to_zero() {}
    std::string str() const {
        std::stringstream ss;
        ss << *this; // simply employ the following operator<<
        return ss.str();
    }
    friend std::ostream& operator<<(std::ostream& os, const Constrained& obj) {
        if (obj.is_internal())
            os << obj.qubit().str();
        else
            os << obj.complex;
        return os;
    }
    Constrained operator+(const Constrained &o) const {
        if (this->is_internal() || o.is_internal()) { THROW_AUTOQ_ERROR("Qubits cannot be added!"); }
        return Constrained(complex.operator+(o.complex));
    }
    // Constrained operator-(const Constrained &o) const { return Constrained(complex.operator-(o.complex)); }
    Constrained operator*(const Constrained &o) const {
        if (this->is_internal() || o.is_internal()) { THROW_AUTOQ_ERROR("Qubits cannot be multiplied!"); }
        return Constrained(complex.operator*(o.complex));
    }
    // bool valueEqual(const Constrained &o) const { return internal == o.internal && complex.valueEqual(o.complex); }
    bool operator==(const Constrained &o) const {
        if (is_internal() != o.is_internal()) return false;
        if (is_internal()) return qubit() == o.qubit();
        return complex == o.complex;
    }
    bool operator<(const Constrained &o) const {
        if (is_internal() && !o.is_internal()) return true;
        if (o.is_internal() && !is_internal()) return false;
        if (is_internal()) return qubit() < o.qubit();
        return complex < o.complex;
    }
    Constrained omega_multiplication(int rotation=1) {
        // if (rotation > 0) complex.counterclockwise(boost::rational<boost::multiprecision::cpp_int>(rotation, 8));
        // if (rotation < 0) complex.clockwise(boost::rational<boost::multiprecision::cpp_int>(rotation, 8));
        return *this;
    }
    Constrained counterclockwise(const boost::rational<boost::multiprecision::cpp_int> &theta) {
        // complex.counterclockwise(theta);
        return *this;
    }
    void fraction_simplification() { complex.fraction_simplification(); }
    Constrained divide_by_the_square_root_of_two() { return *this; }
    void negate() {}
    void degree45cw() {}
    void degree90cw() {}
    Constrained multiply_cos(const boost::rational<boost::multiprecision::cpp_int> &theta) {
        // complex.multiply_cos(theta);
        return *this;
    }
    Constrained multiply_isin(const boost::rational<boost::multiprecision::cpp_int> &theta) {
        // complex.multiply_isin(theta);
        return *this;
    }
};

namespace boost {
    template <> struct hash<AUTOQ::Symbol::Constrained> {
        size_t operator()(const AUTOQ::Symbol::Constrained& obj) const {
            std::size_t seed = 0;
            boost::hash_combine(seed, obj.is_internal());
            boost::hash_combine(seed, obj.complex);
            return seed;
        }
    };
}

#endif