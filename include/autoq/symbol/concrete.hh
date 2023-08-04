#ifndef _AUTOQ_CONCRETE_HH_
#define _AUTOQ_CONCRETE_HH_

#include <vector>
#include <autoq/util/convert.hh>
#include <autoq/complex/complex.hh>
#include <boost/multiprecision/cpp_int.hpp>

namespace AUTOQ
{
	namespace Symbol
	{
        struct Concrete;
	}
}

// Concrete symbol
struct AUTOQ::Symbol::Concrete : Complex::Complex{
// private:
//     // bool Is_internal;
// public:
//     Complex::Complex complex;

//     // Notice that if we do not use is_convertible_v, type int will not be accepted in this case.
//     template <typename T, typename = std::enable_if_t<std::is_convertible<T, int>::value>>
//         Concrete(T qubit) : complex(qubit) {} //, Is_internal(true) {}
//     Concrete(const Complex::Complex &c) : complex(c) {} //, Is_internal(false) {}
//     Concrete() : complex() {} //, Is_internal(false) {}

//     bool is_internal() const { return complex.size() < 5; } //Is_internal; }
//     bool is_leaf() const { return complex.size() == 5; } //!Is_internal; }
//     int qubit() const { return complex.real(); } //Is_internal ? complex.real() : 0; }
//     void back_to_zero() { complex = Complex::Complex::Zero(); }
//     friend std::ostream& operator<<(std::ostream& os, const Concrete& obj) {
//         os << obj.complex;
//         return os;
//     }
    Concrete operator+(const Concrete &o) const { return Concrete(Complex::Complex::operator+(o)); }
    Concrete operator-(const Concrete &o) const { return Concrete(Complex::Complex::operator-(o)); }
//     Concrete operator*(const Concrete &o) const { return Concrete(complex * o.complex); }
//     bool operator==(const Concrete &o) const { return complex == o.complex; }
//     bool operator<(const Concrete &o) const { return complex < o.complex; }
//     // bool operator>(const Concrete &o) const { return complex > o.complex; }
    void omega_multiplication(int rotation=1) {
        if (rotation > 0) counterclockwise(rotation);
        if (rotation < 0) clockwise(rotation);
    }
//     void fraction_simplification() { complex.fraction_simplification(); }
//     void divide_by_the_square_root_of_two() { complex.divide_by_the_square_root_of_two(); }
//     void negate() { negate(); }
    void degree45() { clockwise(1); }
    void degree90() { clockwise(2); }
};

namespace boost {
    template <> struct hash<AUTOQ::Symbol::Concrete> {
        size_t operator()(const AUTOQ::Symbol::Concrete& obj) const {
            std::size_t seed = 0;
            // boost::hash_combine(seed, obj.is_internal());
            boost::hash_combine(seed, obj);
            return seed;
        }
    };
}

#endif