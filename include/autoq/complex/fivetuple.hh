#ifndef _AUTOQ_FIVETUPLE_HH_
#define _AUTOQ_FIVETUPLE_HH_

#include <cmath>
#include <vector>
#include <boost/rational.hpp>
#include "autoq/util/convert.hh"
#include <boost/integer/common_factor.hpp>
#include <boost/multiprecision/cpp_int.hpp>
#include "z3/z3++.h"

namespace AUTOQ
{
	namespace Complex
	{
        struct FiveTuple;
	}
}

typedef std::vector<boost::multiprecision::cpp_int> stdvectorboostmultiprecisioncpp_int;
struct AUTOQ::Complex::FiveTuple : stdvectorboostmultiprecisioncpp_int {
    using stdvectorboostmultiprecisioncpp_int::stdvectorboostmultiprecisioncpp_int;
    typedef typename AUTOQ::Complex::FiveTuple::value_type Entry;
    // Notice that if we do not use is_convertible_v, type int will not be accepted in this case.
    template <typename T, typename = std::enable_if_t<std::is_convertible<T, boost::rational<Entry>>::value>>
        FiveTuple(T in) : stdvectorboostmultiprecisioncpp_int({0,0,0,0,0}) {
            boost::rational<boost::multiprecision::cpp_int> r = in;
            auto d = r.denominator();
            while (d > 0 && d % 2 == 0) {
                at(4) += 2;
                d /= 2;
            }
            if (d != 1) {   // Assume the denominator is a power of 2!
                THROW_AUTOQ_ERROR("The input number cannot be represented with the current data structure!");
            }
            at(0) = r.numerator();
        }
    FiveTuple() : FiveTuple(0) {}
    static FiveTuple Angle(boost::rational<boost::multiprecision::cpp_int> theta) {
        return FiveTuple(1).counterclockwise(theta);
    }
    static FiveTuple One() { return FiveTuple(1); }
    static FiveTuple Zero() { return FiveTuple(0); }
    static FiveTuple Rand() {
        auto number = FiveTuple(0);
        auto val = rand() % 5;
        if (val != 0)
            number.at(rand() % 4) = val;
        return number;
    }
    static FiveTuple sqrt2() { return FiveTuple(1).divide_by_the_square_root_of_two(-1); }
    friend std::ostream& operator<<(std::ostream& os, const FiveTuple& obj) {
        const auto &a=obj[0], &b=obj[1], &c=obj[2], &d=obj[3], &k=obj[4];
        // [a, b, c, d, k] = (a + b*(1+i)/sqrt2 + c*i + d*(-1+i)/sqrt2) / sqrt2^k
        //                 = ((a + (b-d)/sqrt2) + i * (c + (b+d)/sqrt2)) / sqrt2^k
        //                 = (a*sqrt2 + (b-d)) + i * (c*sqrt2 + (b+d)) / sqrt2^(k+1)
        //                 = (2a + (b-d)*sqrt2) + i * (2c + (b+d)*sqrt2) / sqrt2^(k+2)
        // (k+1) % 2 == 0, = [(b-d)/2^((k+1)//2) + sqrt2 * a/2^((k+1)//2)] + i * [(b+d)/2^((k+1)//2) + sqrt2 * c/2^((k+1)//2)]
        // (k+1) % 2 == 1, = [2a/2^((k+2)//2) + sqrt2 * (b-d)/2^((k+2)//2)]  + i * [2c/2^((k+2)//2) + sqrt2 * (b+d)/2^((k+2)//2)]
        if (k < -2) {
            os << AUTOQ::Util::Convert::ToString(static_cast<stdvectorboostmultiprecisioncpp_int>(obj));
        } else if ((k+1) % 2 == 0) {
            if (b-d != 0) os << boost::rational<boost::multiprecision::cpp_int>(b-d, boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>((k+1)/2)));
            if (b-d != 0 && a != 0) os << "+";
            if (a != 0) os << "sqrt2*" << boost::rational<boost::multiprecision::cpp_int>(a, boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>((k+1)/2)));
            if ((b-d != 0 || a != 0) && (b+d != 0 || c != 0)) os << " + ";
            if (b+d != 0 || c != 0) os << "i * (";
            if (b+d != 0) os << boost::rational<boost::multiprecision::cpp_int>(b+d, boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>((k+1)/2)));
            if (b+d != 0 && c != 0) os << "+";
            if (c != 0) os << "sqrt2*" << boost::rational<boost::multiprecision::cpp_int>(c, boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>((k+1)/2)));
            if ((b-d != 0 || a != 0) && (b+d != 0 || c != 0)) os << ")";
            if (b-d == 0 && a == 0 && b+d == 0 && c == 0) os << "0";
        } else {
            if (2*a != 0) os << boost::rational<boost::multiprecision::cpp_int>(2*a, boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>((k+2)/2)));
            if (2*a != 0 && b-d != 0) os << "+";
            if (b-d != 0) os << "sqrt2*" << boost::rational<boost::multiprecision::cpp_int>(b-d, boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>((k+2)/2)));
            if ((2*a != 0 || b-d != 0) && (2*c != 0 || b+d != 0)) os << " + ";
            if (2*c != 0 || b+d != 0) os << "i * (";
            if (2*c != 0) os << boost::rational<boost::multiprecision::cpp_int>(2*c, boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>((k+2)/2)));
            if (2*c != 0 && b+d != 0) os << "+";
            if (b+d != 0) os << "sqrt2*" << boost::rational<boost::multiprecision::cpp_int>(b+d, boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>((k+2)/2)));
            if ((2*a != 0 || b-d != 0) && (2*c != 0 || b+d != 0)) os << ")";
            if (2*a == 0 && b-d == 0 && 2*c == 0 && b+d == 0) os << "0";
        }
        return os;
    }
    FiveTuple operator+(const FiveTuple &o) const { return binary_operation(o, true); }
    FiveTuple& operator+=(const FiveTuple &o) { *this = binary_operation(o, true); return *this; }
    FiveTuple operator-(const FiveTuple &o) const { return binary_operation(o, false); }
    FiveTuple operator*(const FiveTuple &o) const {
        FiveTuple symbol;
        symbol.at(0) = at(0)*o.at(0) - at(1)*o.at(3) - at(2)*o.at(2) - at(3)*o.at(1);
        symbol.at(1) = at(0)*o.at(1) + at(1)*o.at(0) - at(2)*o.at(3) - at(3)*o.at(2);
        symbol.at(2) = at(0)*o.at(2) + at(1)*o.at(1) + at(2)*o.at(0) - at(3)*o.at(3);
        symbol.at(3) = at(0)*o.at(3) + at(1)*o.at(2) + at(2)*o.at(1) + at(3)*o.at(0);
        symbol.at(4) = at(4) + o.at(4); // remember to push k
        return symbol;
    }
    FiveTuple operator/(FiveTuple o) const {
        // std::cout << *this << o;
        auto a = o.at(0);
        auto b = o.at(1);
        auto c = o.at(2);
        auto d = o.at(3);
        o.at(0) = a*a*a + 2*a*b*d + a*c*c + c*d*d - b*b*c;
        o.at(1) = -a*a*b - b*b*d + b*c*c - d*d*d - 2*a*c*d;
        o.at(2) = -a*a*c + 2*b*c*d - c*c*c - a*d*d + a*b*b;
        o.at(3) = -b*d*d + 2*a*b*c - b*b*b - a*a*d + c*c*d;
        o.at(4) = -o.at(4);
        o = (*this) * o;
        boost::multiprecision::cpp_int dd = (a*a + 2*b*d - c*c) * (a*a + 2*b*d - c*c) + (d*d + 2*a*c - b*b) * (d*d + 2*a*c - b*b);
        boost::multiprecision::cpp_int cf = boost::integer::gcd(boost::integer::gcd(boost::integer::gcd(boost::integer::gcd(o.at(0), o.at(1)), o.at(2)), o.at(3)), dd);
        for (int i=0; i<4; i++) o.at(i) /= cf;
        dd /= cf;
        while ((dd & 1) == 0) {
            o.at(4) += 2;
            dd >>= 1;
        }
        assert(dd == 1); // Assume the denominator is a power of 2!
        // std::cout << o << std::endl;
        return o;
    }
    FiveTuple& fraction_simplification() { // TODO: still necessary for inclusion checking
        if (at(0)==0 && at(1)==0 && at(2)==0 && at(3)==0) at(4) = 0;
        else {
            while ((at(0)&1)==0 && (at(1)&1)==0 && (at(2)&1)==0 && (at(3)&1)==0 && at(4)>=2) { // Notice the parentheses enclosing at(i)&1 are very important! HAHA
                for (int i=0; i<4; i++) at(i) /= 2;
                at(4) -= 2;
            }
        }
        return *this;
    }
    FiveTuple& divide_by_the_square_root_of_two(int times=1) {
        // assert(times >= 0);
        at(4) += times;
        return *this;
    }
    FiveTuple& clockwise(boost::rational<boost::multiprecision::cpp_int> theta) {
        theta -= theta.numerator() / theta.denominator();
        while (theta >= 1)
            theta -= 1;
        while (theta < 0)
            theta += 1;
        assert((8 * theta).denominator() == 1);
        int r = static_cast<int>(-8 * theta.numerator() / theta.denominator());
        while (r != 0) {
            if (r > 0) {
                auto temp = at(3);
                for (int i=3; i>=1; i--) { // exclude "k"
                    at(i) = at(i-1);
                }
                at(0) = -temp;
                r--;
            } else {
                auto temp = at(0);
                for (int i=0; i<=2; i++) { // exclude "k"
                    at(i) = at(i+1);
                }
                at(3) = -temp;
                r++;
            }
        }
        return *this;
    }
    FiveTuple& counterclockwise(boost::rational<boost::multiprecision::cpp_int> theta) {
        theta -= theta.numerator() / theta.denominator();
        while (theta >= 1)
            theta -= 1;
        while (theta < 0)
            theta += 1;
        assert((8 * theta).denominator() == 1);
        int r = static_cast<int>(8 * theta.numerator() / theta.denominator());
        while (r != 0) {
            if (r > 0) {
                auto temp = at(3);
                for (int i=3; i>=1; i--) { // exclude "k"
                    at(i) = at(i-1);
                }
                at(0) = -temp;
                r--;
            } else {
                auto temp = at(0);
                for (int i=0; i<=2; i++) { // exclude "k"
                    at(i) = at(i+1);
                }
                at(3) = -temp;
                r++;
            }
        }
        return *this;
    }
    boost::multiprecision::cpp_int toInt() const { // TODO: fake solution
        return at(0);
    }
    boost::rational<boost::multiprecision::cpp_int> to_rational() const { // TODO: fake solution
        return boost::rational<boost::multiprecision::cpp_int>(at(0), boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>(at(4)/2)));
    }
    std::string realToSMT() const {
        z3::context ctx;
        return realToSMT(ctx).to_string();
    }
    z3::expr realToSMT(z3::context &ctx) const {
        boost::multiprecision::cpp_int num = boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>(at(4)/2));
        auto sqrt2 = ctx.real_const("sqrt2");
        auto result0 = (at(4) % 2 == 0) ?
                       (ctx.real_val(at(0).str().c_str()) * 2 + (ctx.real_val(at(1).str().c_str()) - ctx.real_val(at(3).str().c_str())) * sqrt2) / (ctx.real_val(num.str().c_str()) * 2) :
                       (ctx.real_val(at(0).str().c_str()) * sqrt2 + (ctx.real_val(at(1).str().c_str()) - ctx.real_val(at(3).str().c_str()))) / (ctx.real_val(num.str().c_str()) * 2);
        auto result = result0.simplify();
        return result;
    }
    std::string imagToSMT() const {
        z3::context ctx;
        return imagToSMT(ctx).to_string();
    }
    z3::expr imagToSMT(z3::context &ctx) const {
        boost::multiprecision::cpp_int num = boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>(at(4)/2));
        auto sqrt2 = ctx.real_const("sqrt2");
        auto result0 = (at(4) % 2 == 0) ?
                       (ctx.real_val(at(2).str().c_str()) * 2 + (ctx.real_val(at(1).str().c_str()) + ctx.real_val(at(3).str().c_str())) * sqrt2) / (ctx.real_val(num.str().c_str()) * 2) :
                       (ctx.real_val(at(2).str().c_str()) * sqrt2 + (ctx.real_val(at(1).str().c_str()) + ctx.real_val(at(3).str().c_str()))) / (ctx.real_val(num.str().c_str()) * 2);
        auto result = result0.simplify();
        return result;
    }
    double abs2() const {
        double a = static_cast<double>(at(0)) / pow(2, static_cast<double>(at(4))/2.0);
        double b = static_cast<double>(at(1)) / pow(2, static_cast<double>(at(4))/2.0);
        double c = static_cast<double>(at(2)) / pow(2, static_cast<double>(at(4))/2.0);
        double d = static_cast<double>(at(3)) / pow(2, static_cast<double>(at(4))/2.0);
        return static_cast<double>(pow(a, 2) + pow(b, 2) + pow(c, 2) + pow(d, 2))
            + pow(2, 0.5) * static_cast<double>(a * (b - d) + c * (b + d));
    }
    bool isZero() const {
        return at(0)==0 && at(1)==0 && at(2)==0 && at(3)==0;
    }
    FiveTuple real() const {
        // Sum up the following three 5-tuples.
        // {at(0), 0, 0, 0, at(4)} = {0, at(0), 0, -at(0), at(4)+1}
        // {at(1), 0, 0, 0, at(4)+1}
        // {-at(3), 0, 0, 0, at(4)+1}
        // Result: {at(1)-at(3), at(0), 0, -at(0), at(4)+1}
        return {at(1)-at(3), at(0), 0, -at(0), at(4)+1};
    }
    FiveTuple imag() const {
        // Sum up the following three 5-tuples.
        // {0, 0, at(2), 0, at(4)} = {0, at(2), 0, at(2), at(4)+1}
        // {0, 0, at(1), 0, at(4)+1}
        // {0, 0, at(3), 0, at(4)+1}
        // Result: {0, at(2), at(1)+at(3), at(2), at(4)+1}
        return {0, at(2), at(1)+at(3), at(2), at(4)+1};
    }
    void increase_k() {
        FiveTuple symbol;
        symbol.at(1) += at(0);
        symbol.at(3) -= at(0);
        symbol.at(0) += at(1);
        symbol.at(2) += at(1);
        symbol.at(1) += at(2);
        symbol.at(3) += at(2);
        symbol.at(2) += at(3);
        symbol.at(0) -= at(3);
        symbol.at(4) += at(4) + 1;
        *this = symbol;
    }
    void increase_to_k(const boost::multiprecision::cpp_int &k) {
        while (this->k() < k)
            increase_k();
    }
    FiveTuple& multiply_cos(const boost::rational<boost::multiprecision::cpp_int> &theta) {
        auto c1 = *this;
        auto c2 = *this;
        *this = (c1.counterclockwise(theta) + c2.counterclockwise(-theta)).divide_by_the_square_root_of_two(2);
        return *this;
    }
    FiveTuple& multiply_isin(const boost::rational<boost::multiprecision::cpp_int> &theta) {
        auto c1 = *this;
        auto c2 = *this;
        *this = (c1.counterclockwise(theta) - c2.counterclockwise(-theta)).divide_by_the_square_root_of_two(2);
        return *this;
    }
    boost::multiprecision::cpp_int& k() { return at(4); }
    void back_to_zero() {
        for (int i=0; i<4; i++) at(i) = 0;
    }

private:
    FiveTuple binary_operation(FiveTuple o, bool add) const {
        auto This = *this;
        while (This.at(4) < o.at(4)) {
            This.increase_k();
        }
        while (This.at(4) > o.at(4)) {
            o.increase_k();
        }
        FiveTuple symbol;
        for (int i=0; i<4; i++) {
            if (add) symbol.at(i) = This.at(i) + o.at(i);
            else symbol.at(i) = This.at(i) - o.at(i);
        }
        symbol.at(4) = std::max(This.at(4), o.at(4)); // remember to push k
        return symbol;
    }
public:
    bool valueEqual(FiveTuple o) const {
        if (size() != o.size()) return false;
        if (size() != 5) return static_cast<stdvectorboostmultiprecisioncpp_int>(*this) == static_cast<stdvectorboostmultiprecisioncpp_int>(o);
        auto This = *this;
        if (This.k() < o.k()) {
            This.increase_to_k(o.k());
        } else if (This.k() > o.k()) {
            o.increase_to_k(This.k());
        }
        return This.at(0)==o.at(0) && This.at(1)==o.at(1) && This.at(2)==o.at(2) && This.at(3)==o.at(3);
    }
};

#endif