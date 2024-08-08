#ifndef _AUTOQ_PLAIN_HH_
#define _AUTOQ_PLAIN_HH_

#include <cmath>
#include <vector>
#include <boost/rational.hpp>
#include "autoq/util/convert.hh"
#include <boost/multiprecision/cpp_int.hpp>

namespace AUTOQ
{
	namespace Complex
	{
        struct Plain;
	}
}

#define PRECISION 14

#pragma GCC diagnostic ignored "-Wfloat-equal"
typedef std::pair<double, double> stdpairdouble128double128;
struct AUTOQ::Complex::Plain : std::pair<double, double> {
    using stdpairdouble128double128::stdpairdouble128double128;
    // Notice that if we do not use is_convertible_v, type int will not be accepted in this case.
    template <typename T, typename = std::enable_if_t<std::is_convertible<T, boost::rational<boost::multiprecision::cpp_int>>::value>>
        Plain(T in) : std::pair<double, double>(static_cast<double>(boost::rational<boost::multiprecision::cpp_int>(in).numerator()) / static_cast<double>(boost::rational<boost::multiprecision::cpp_int>(in).denominator()), 0) {}
    static Plain Angle(boost::rational<boost::multiprecision::cpp_int> theta) {
        return Plain(std::cos(2 * M_PI * static_cast<double>(theta.numerator()) / static_cast<double>(theta.denominator())),
                     std::sin(2 * M_PI * static_cast<double>(theta.numerator()) / static_cast<double>(theta.denominator())));
    }
    static Plain One() { return Plain(1, 0); }
    static Plain Zero() { return Plain(0, 0); }
    static Plain Rand() { return Plain(rand() * 1.0 / RAND_MAX, rand() * 1.0 / RAND_MAX); }
    static Plain sqrt2() { return Plain(std::sqrt(2.0), 0); }
    friend std::ostream& operator<<(std::ostream& os, const Plain& obj) {
        os << "[" << AUTOQ::Util::Convert::ToString(obj.first) << "," << AUTOQ::Util::Convert::ToString(obj.second) << "]";
        return os;
    }
    Plain operator+(const Plain &o) const { return binary_operation(o, true); }
    Plain operator-(const Plain &o) const { return binary_operation(o, false); }
    Plain operator*(const Plain &o) const { return Plain(first*o.first - second*o.second, first*o.second + second*o.first); }
    Plain operator/(const Plain &o) const { // (a+bi)/(c+di) = (a+bi)(c-di) / (c^2+d^2) = (ac+bd + i(bc-ad)) / (c^2+d^2)
        return Plain((first*o.first+second*o.second) / (o.first*o.first+o.second*o.second),
                     (second*o.first-first*o.second) / (o.first*o.first+o.second*o.second));
    }
    Plain& fraction_simplification() {
        first = round_to(first, std::pow(10, PRECISION));
        if (first == -0.0) first = 0.0;
        second = round_to(second, std::pow(10, PRECISION));
        if (second == -0.0) second = 0.0;
        return *this;
    }
    Plain& divide_by_the_square_root_of_two(int times=1) {
        assert(times >= 0);
        first /= std::pow(std::sqrt(2.0), times);
        second /= std::pow(std::sqrt(2.0), times);
        return *this;
    }
    Plain& clockwise(boost::rational<boost::multiprecision::cpp_int> theta) {
        *this = Plain::operator*(Plain::Angle(-theta));
        return *this;
    }
    Plain& counterclockwise(boost::rational<boost::multiprecision::cpp_int> theta) {
        *this = Plain::operator*(Plain::Angle(theta));
        return *this;
    }
    boost::multiprecision::cpp_int toInt() const { // TODO: fake solution
        return static_cast<boost::multiprecision::cpp_int>(first);
    }
    boost::rational<boost::multiprecision::cpp_int> to_rational() const { // TODO: fake solution
        return boost::rational<boost::multiprecision::cpp_int>(static_cast<boost::multiprecision::cpp_int>(first * 1000000), 1000000);
    }
    std::string realToSMT() const {
        std::ostringstream stm;
        stm << std::setprecision(PRECISION) << first;
        auto result = stm.str();
        // auto result = std::to_string(first);
        size_t found = result.find("e");
        if (found != std::string::npos) {
            std::string mantissa = result.substr(0, found);
            std::string exponent = result.substr(found + 1); // "e".length()
            return "(* " + mantissa + " (^ 10 " + exponent + "))";
        }
        return result;
    }
    std::string imagToSMT() const {
        std::ostringstream stm;
        stm << std::setprecision(PRECISION) << second;
        auto result = stm.str();
        // auto result = std::to_string(second);
        size_t found = result.find("e");
        if (found != std::string::npos) {
            std::string mantissa = result.substr(0, found);
            std::string exponent = result.substr(found + 1); // "e".length()
            return "(* " + mantissa + " (^ 10 " + exponent + "))";
        }
        return result;
    }
    double abs2() const {
        return first*first + second*second;
    }
    bool operator==(const Plain &o) const {
        return first == o.first && second == o.second;
    }
    bool operator<(const Plain &o) const {
        if (first < o.first) return true;
        else if (first > o.first) return false;
        else return second < o.second;
    }
    bool isZero() const {
        return first == 0 && second == 0;
    }

private:
    Plain binary_operation(const Plain &o, bool add) const {
        if (add) return Plain(first+o.first, second+o.second);
        else return Plain(first-o.first, second-o.second);
    }
    // bool operator==(const Plain &o) const {
    //     return first == o.first && second == o.second;
    // }
    double round_to(double value, double precision = 1.0) {
        return std::round(value * precision) / precision;
    }
};
#pragma GCC diagnostic pop

#endif