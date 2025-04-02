#ifndef _AUTOQ_CONCRETE_HH_
#define _AUTOQ_CONCRETE_HH_

#include <vector>
#include "autoq/util/convert.hh"
#include "autoq/complex/complex.hh"
#include <boost/multiprecision/cpp_int.hpp>
#include <boost/functional/hash.hpp>

namespace AUTOQ
{
	namespace Symbol
	{
        struct Concrete;
	}
}

// Concrete symbol
struct AUTOQ::Symbol::Concrete {
private:
    bool internal;
public:
    Complex::Complex complex;

    // Notice that if we do not use is_convertible_v, type int will not be accepted in this case.
    template <typename T, typename = std::enable_if_t<std::is_convertible<T, boost::multiprecision::cpp_int>::value>>
    Concrete(T qubit) : internal(true), complex(qubit) {}
    Concrete(const Complex::Complex &c) : internal(false), complex(c) {}
    Concrete() : internal(), complex() {} // prevent the compiler from complaining about the lack of default constructor
    bool is_internal() const { return internal; }
    bool is_leaf() const { return !internal; }
    boost::multiprecision::cpp_int qubit() const {
        if (!internal) {
            THROW_AUTOQ_ERROR("Leaf symbols do not have qubit().");
        }
        // assert(complex.real().denominator() == 1);
        return complex.toInt(); //.numerator();
    }
    void back_to_zero() { complex = Complex::Complex::Zero(); }
    std::string str() const {
        std::stringstream ss;
        ss << *this; // simply employ the following operator<<
        return ss.str();
    }
    friend std::ostream& operator<<(std::ostream& os, const Concrete& obj) {
        if (obj.internal)
            os << obj.qubit().str();
        else
            os << obj.complex;
        return os;
    }
    Concrete operator+(const Concrete &o) const { return Concrete(complex.operator+(o.complex)); }
    Concrete operator-(const Concrete &o) const { return Concrete(complex.operator-(o.complex)); }
    Concrete operator*(const Concrete &o) const { return Concrete(complex.operator*(o.complex)); }
    bool valueEqual(const Concrete &o) const { return internal == o.internal && complex.valueEqual(o.complex); }
    bool operator==(const Concrete &o) const { return internal == o.internal && complex == o.complex; }
    bool operator<(const Concrete &o) const {
        if (internal && !o.internal) return true;
        if (o.internal && !internal) return false;
        return complex < o.complex;
    }
    Concrete omega_multiplication(int rotation=1) {
        if (rotation > 0) complex.counterclockwise(boost::rational<boost::multiprecision::cpp_int>(rotation, 8));
        if (rotation < 0) complex.clockwise(boost::rational<boost::multiprecision::cpp_int>(rotation, 8));
        return *this;
    }
    Concrete counterclockwise(const boost::rational<boost::multiprecision::cpp_int> &theta) {
        complex.counterclockwise(theta);
        return *this;
    }
    void fraction_simplification() { complex.fraction_simplification(); }
    Concrete divide_by_the_square_root_of_two() { complex.divide_by_the_square_root_of_two(); return *this; }
    void negate() { complex = complex * (-1); }
    void degree45cw() { complex.clockwise(boost::rational<boost::multiprecision::cpp_int>(1, 8)); }
    void degree90cw() { complex.clockwise(boost::rational<boost::multiprecision::cpp_int>(1, 4)); }
    Concrete multiply_cos(const boost::rational<boost::multiprecision::cpp_int> &theta) {
        complex.multiply_cos(theta);
        return *this;
    }
    Concrete multiply_isin(const boost::rational<boost::multiprecision::cpp_int> &theta) {
        complex.multiply_isin(theta);
        return *this;
    }
};

namespace boost {
    template <> struct hash<AUTOQ::Symbol::Concrete> {
        size_t operator()(const AUTOQ::Symbol::Concrete& obj) const {
            std::size_t seed = 0;
            boost::hash_combine(seed, obj.is_internal());
            boost::hash_combine(seed, obj.complex);
            return seed;
        }
    };
}

#endif