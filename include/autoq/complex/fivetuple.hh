#ifndef _AUTOQ_FIVETUPLE_HH_
#define _AUTOQ_FIVETUPLE_HH_

#include <cmath>
#include <vector>
#include <boost/rational.hpp>
#include <autoq/util/convert.hh>
#include <boost/integer/common_factor.hpp>
#include <boost/multiprecision/cpp_int.hpp>

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
            assert(d == 1); // Assume the denominator is a power of 2!
            at(0) = r.numerator();
        }
    static FiveTuple Angle(boost::rational<boost::multiprecision::cpp_int> theta) {
        theta -= theta.numerator() / theta.denominator();
        while (theta >= 1)
            theta -= 1;
        while (theta < 0)
            theta += 1;
        if (theta.numerator() == 0) return {1,0,0,0,0};
        if (theta == boost::rational<boost::multiprecision::cpp_int>(1, 8)) return {0,1,0,0,0};
        if (theta == boost::rational<boost::multiprecision::cpp_int>(2, 8)) return {0,0,1,0,0};
        if (theta == boost::rational<boost::multiprecision::cpp_int>(3, 8)) return {0,0,0,1,0};
        if (theta == boost::rational<boost::multiprecision::cpp_int>(4, 8)) return {-1,0,0,0,0};
        if (theta == boost::rational<boost::multiprecision::cpp_int>(5, 8)) return {0,-1,0,0,0};
        if (theta == boost::rational<boost::multiprecision::cpp_int>(6, 8)) return {0,0,-1,0,0};
        if (theta == boost::rational<boost::multiprecision::cpp_int>(7, 8)) return {0,0,0,-1,0};
        throw std::runtime_error(AUTOQ_LOG_PREFIX + "Angle not supported!");
    }
    static FiveTuple One() { return FiveTuple({1,0,0,0,0}); }
    static FiveTuple Zero() { return FiveTuple({0,0,0,0,0}); }
    static FiveTuple Rand() { return FiveTuple({rand()%5, rand()%5, rand()%5, rand()%5, 0}); }
    static FiveTuple sqrt2() { return FiveTuple({1,0,0,0,-1}); }
    friend std::ostream& operator<<(std::ostream& os, const FiveTuple& obj) {
        os << AUTOQ::Util::Convert::ToString(static_cast<stdvectorboostmultiprecisioncpp_int>(obj));
        return os;
    }
    FiveTuple operator+(const FiveTuple &o) const { return binary_operation(o, true); }
    FiveTuple operator-(const FiveTuple &o) const { return binary_operation(o, false); }
    FiveTuple operator*(const FiveTuple &o) const {
        FiveTuple symbol;
        symbol.push_back(at(0)*o.at(0) - at(1)*o.at(3) - at(2)*o.at(2) - at(3)*o.at(1));
        symbol.push_back(at(0)*o.at(1) + at(1)*o.at(0) - at(2)*o.at(3) - at(3)*o.at(2));
        symbol.push_back(at(0)*o.at(2) + at(1)*o.at(1) + at(2)*o.at(0) - at(3)*o.at(3));
        symbol.push_back(at(0)*o.at(3) + at(1)*o.at(2) + at(2)*o.at(1) + at(3)*o.at(0));
        symbol.push_back(at(4) + o.at(4)); // remember to push k
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
        assert(times >= 0);
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
        std::string result = "(/ (+ ";
        result += at(0).str();
        result += " (* " + std::to_string(std::sqrt(2.0) / 2.0) + " " + at(1).str() + ")";
        result += " (* (- " + std::to_string(std::sqrt(2.0) / 2.0) + ") " + at(3).str() + ")";
        result += ") " + std::to_string(std::pow(std::sqrt(2.0), static_cast<int>(at(4)))) + ")";
        return result;
    }
    std::string imagToSMT() const {
        std::string result = "(/ (+";
        result += " (* " + std::to_string(std::sqrt(2.0) / 2.0) + " " + at(1).str() + ") ";
        result += at(2).str();
        result += " (* " + std::to_string(std::sqrt(2.0) / 2.0) + " " + at(3).str() + ")";
        result += ") " + std::to_string(std::pow(std::sqrt(2.0), static_cast<int>(at(4)))) + ")";
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

private:
    FiveTuple binary_operation(const FiveTuple &o, bool add) const {
        assert((at(4) == o.at(4)) ||
            (at(0)==0 && at(1)==0 && at(2)==0 && at(3)==0 && at(4)<=o.at(4)) ||
            (o.at(0)==0 && o.at(1)==0 && o.at(2)==0 && o.at(3)==0 && at(4)>=o.at(4)));
        FiveTuple symbol;
        for (int i=0; i<4; i++) {
            if (add) symbol.push_back(at(i) + o.at(i));
            else symbol.push_back(at(i) - o.at(i));
        }
        symbol.push_back(std::max(at(4), o.at(4))); // remember to push k
        return symbol;
    }
public:
    bool valueEqual(const FiveTuple &o) const {
        if (size() != o.size()) return false;
        if (size() != 5) return static_cast<stdvectorboostmultiprecisioncpp_int>(*this) == static_cast<stdvectorboostmultiprecisioncpp_int>(o);
        if (at(0)==0 && at(1)==0 && at(2)==0 && at(3)==0 &&
            o.at(0)==0 && o.at(1)==0 && o.at(2)==0 && o.at(3)==0)
            return true;
        else {
            if ((at(4)&1) != (o.at(4)&1)) return false;
            auto min_d = min(at(4), o.at(4));
            return (at(0) << static_cast<int>((o.at(4)-min_d)/2)) == (o.at(0) << static_cast<int>((at(4)-min_d)/2))
                && (at(1) << static_cast<int>((o.at(4)-min_d)/2)) == (o.at(1) << static_cast<int>((at(4)-min_d)/2))
                && (at(2) << static_cast<int>((o.at(4)-min_d)/2)) == (o.at(2) << static_cast<int>((at(4)-min_d)/2))
                && (at(3) << static_cast<int>((o.at(4)-min_d)/2)) == (o.at(3) << static_cast<int>((at(4)-min_d)/2));
        }
    }
};

#endif