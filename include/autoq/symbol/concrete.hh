#ifndef _AUTOQ_CONCRETE_HH_
#define _AUTOQ_CONCRETE_HH_

#include <vector>
#include "autoq/symbol/symbol_base.hh"
#include "autoq/util/convert.hh"
#include "autoq/complex/complex.hh"
#include <boost/multiprecision/cpp_int.hpp>


#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wold-style-cast"
#include <boost/functional/hash.hpp>
#pragma GCC diagnostic pop

namespace AUTOQ
{
	namespace Symbol
	{
        struct Concrete;
	}
}

// Concrete symbol
struct AUTOQ::Symbol::Concrete : AUTOQ::Symbol::SymbolBase<Concrete> {
    Complex::Complex complex;
    inline static std::map<std::pair<Concrete, Concrete>, Concrete> mulmap;

    // Notice that if we do not use is_convertible_v, type int will not be accepted in this case.
    template <typename T, typename = std::enable_if_t<std::is_convertible<T, boost::multiprecision::cpp_int>::value>>
    Concrete(T qubit) : SymbolBase<Concrete>(true), complex(qubit) {}
    Concrete(const Complex::Complex &c) : SymbolBase<Concrete>(false), complex(c) {}
    Concrete() : SymbolBase<Concrete>(false), complex(0) {} // prevent the compiler from complaining about the lack of default constructor

    boost::multiprecision::cpp_int qubit() const {
        if (!is_internal()) {
            THROW_AUTOQ_ERROR("Leaf symbols do not have qubit().");
        }
        // assert(complex.real().denominator() == 1);
        return complex.toInt(); //.numerator();
    }
    void back_to_zero() { complex.back_to_zero(); } // = Complex::Complex::Zero(); }
    std::string str() const {
        std::stringstream ss;
        ss << *this; // simply employ the following operator<<
        return ss.str();
    }
    friend std::ostream& operator<<(std::ostream& os, const Concrete& obj) {
        if (obj.is_internal())
            os << obj.qubit().str();
        else
            os << obj.complex;
        return os;
    }
    Concrete operator+(const Concrete &o) const { return Concrete(complex.operator+(o.complex)); }
    Concrete operator-(const Concrete &o) const { return Concrete(complex.operator-(o.complex)); }
    Concrete operator*(const Concrete &o) const {
        if (!mulmap.empty()) {
            auto it = mulmap.find(std::make_pair(*this, o));
            if (it != mulmap.end()) return it->second;
            // it = mulmap.find(std::make_pair(o, *this));
            // if (it != mulmap.end()) return it->second;
        }
        return Concrete(complex.operator*(o.complex));
    }
    bool valueEqual(const Concrete &o) const { return is_internal() == o.is_internal() && complex.valueEqual(o.complex); }
    bool operator==(const Concrete &o) const { return is_internal() == o.is_internal() && complex == o.complex; }
    bool operator<(const Concrete &o) const {
        if (is_internal() && !o.is_internal()) return true;
        if (o.is_internal() && !is_internal()) return false;
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
