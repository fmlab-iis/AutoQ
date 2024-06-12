#ifndef _AUTOQ_NTUPLE_HH_
#define _AUTOQ_NTUPLE_HH_

#include <cmath>
#include <vector>
#include <algorithm>
#include <boost/rational.hpp>
#include <autoq/util/convert.hh>
#include <boost/integer/common_factor.hpp>
#include <boost/multiprecision/cpp_int.hpp>

namespace AUTOQ
{
	namespace Complex
	{
        struct nTuple;
	}
}

typedef std::vector<boost::multiprecision::cpp_int> stdvectorboostmultiprecisioncpp_int;
struct AUTOQ::Complex::nTuple : stdvectorboostmultiprecisioncpp_int {
    inline static int N = 1; // the smallest angle unit = pi / N. Notice that N >= 4 if adjust_k is to be executed.
    using stdvectorboostmultiprecisioncpp_int::stdvectorboostmultiprecisioncpp_int;
    typedef typename AUTOQ::Complex::nTuple::value_type Entry;
    // Notice that if we do not use is_convertible_v, type int will not be accepted in this case.
    template <typename T, typename = std::enable_if_t<std::is_convertible<T, boost::rational<Entry>>::value>>
        nTuple(T in) : stdvectorboostmultiprecisioncpp_int(N+1, 0) {
            boost::rational<boost::multiprecision::cpp_int> r = in;
            auto d = r.denominator();
            while (d > 0 && d % 2 == 0) {
                back() += 2;
                d /= 2;
            }
            if (d != 1) { // Assume the denominator is a power of 2!
                AUTOQ_ERROR("The denominator is not a power of 2!");
                exit(1);
            }
            // The above just transform the denominator d into √2^back().
            front() = r.numerator();
        }
    nTuple() : nTuple(0) {}
    static nTuple Angle(boost::rational<boost::multiprecision::cpp_int> theta) {
        return nTuple(1).counterclockwise(theta);
    }
    static nTuple One() { return nTuple(1); }
    static nTuple Zero() { return nTuple(0); }
    static nTuple Rand() {
        auto ini = nTuple(0);
        std::for_each(ini.begin(), std::prev(ini.end()), [](auto &n) { n = rand() % 5; });
        return ini;
    }
    static nTuple sqrt2() { return nTuple(1).divide_by_the_square_root_of_two(-1); }
    friend std::ostream& operator<<(std::ostream& os, const nTuple& obj) {
        os << AUTOQ::Util::Convert::ToString(static_cast<stdvectorboostmultiprecisioncpp_int>(obj));
        return os;
    }
    nTuple operator+(const nTuple &o) const { return binary_operation(o, true); }
    nTuple operator-(const nTuple &o) const { return binary_operation(o, false); }
    nTuple operator*(const nTuple &o) const {
        nTuple symbol;
        for (int i=0; i<N; i++)
            for (int j=0; j<N; j++) {
                int targetAngle = i + j;
                boost::multiprecision::cpp_int targetAmplitude = this->at(i) * o.at(j);
                while (targetAngle >= N) {
                    targetAngle -= N;
                    targetAmplitude = -targetAmplitude;
                }
                symbol.at(targetAngle) += targetAmplitude;
            }
        symbol.back() = this->back() + o.back(); // remember to set k
        return symbol;
    }
    nTuple operator/(nTuple denominator) const {
        auto numerator = *this;
        int grid = 1;
        // std::cout << AUTOQ::Util::Convert::ToString(numerator) << std::endl;
        // std::cout << AUTOQ::Util::Convert::ToString(denominator) << std::endl;
        while (!std::all_of(std::next(denominator.begin()), std::prev(denominator.end()), [](auto item) { return item == 0; })) {
            auto temp = denominator;
            for (int i=1; grid*i<=N-1; i+=2) {
                temp.at(grid*i) *= -1;
            }
            numerator = numerator * temp;
            denominator = denominator * temp;
            if (grid & (1<<30)) {
                AUTOQ_ERROR("The number of iterations in operator/ is too high!");
                exit(1);
            }
            grid <<= 1;
        }
        // Now, denominator is a real number.
        // That is, only front() and back() are non-zero.
        numerator.back() -= denominator.back();
        denominator.back() = 0;
        if (denominator.front() == 0) {
            AUTOQ_ERROR("The denominator should not be zero!");
            exit(1);
        }
        while (denominator.front() % 2 == 0) {
            denominator.front() /= 2;
            numerator.back() += 2;
        }
        if (std::all_of(numerator.begin(), std::prev(numerator.end()), [denominator](auto item) { return item % denominator.front() == 0; })) {
            std::for_each(numerator.begin(), std::prev(numerator.end()), [denominator](auto &n) { n /= denominator.front(); });
            // numerator.fraction_simplification();
            return numerator;
        } else {
            AUTOQ_ERROR("The result is not expressible!");
            exit(1);
        }
    }
    nTuple& fraction_simplification() { // TODO: still necessary for inclusion checking
        if (isZero()) back() = 0;
        else {
            if (back() < 0) {
                int k = (1 + static_cast<int>(-back()))/2;
                std::for_each(this->begin(), std::prev(this->end()), [k](auto &n) { n *= boost::multiprecision::pow(boost::multiprecision::cpp_int(2), k); });
                back() += k * 2;
            }
            while (std::all_of(this->begin(), std::prev(this->end()), [](auto item) { return (item & 1) == 0; }) && back() >= 2) {
                std::for_each(this->begin(), std::prev(this->end()), [](auto &n) { n /= 2; });
                back() -= 2;
            }
        }
        return *this;
    }
    nTuple& divide_by_the_square_root_of_two(int times=1) {
        back() += times;
        return *this;
    }
    nTuple& clockwise(boost::rational<boost::multiprecision::cpp_int> theta) {
        theta -= theta.numerator() / theta.denominator();
        while (theta > 1)
            theta -= 1;
        while (theta <= 0)
            theta += 1;
        // Ensure that theta is in (0, 1].
        // Then, 1-theta is in [0, 1).
        return counterclockwise(1 - theta);
    }
    nTuple& counterclockwise(boost::rational<boost::multiprecision::cpp_int> theta) {
        theta -= theta.numerator() / theta.denominator();
        while (theta >= 1)
            theta -= 1;
        while (theta < 0)
            theta += 1;
        // Ensure that theta is in [0, 1).
        if ((N*2 * theta).denominator() != 1) {
            AUTOQ_ERROR("This angle is not supported!");
            exit(1);
        }
        auto t = static_cast<int>(N*2 * theta.numerator() / theta.denominator());
        // Solve theta = t / (N*2).
        nTuple result;
        for (int i=0; i<N; i++) {
            int targetAngle = i + t;
            auto targetAmplitude = this->at(i);
            while (targetAngle >= N) {
                targetAngle -= N;
                targetAmplitude *= -1;
            }
            result.at(targetAngle) += targetAmplitude;
        }
        result.back() = this->back();
        *this = result;
        return *this;
    }
    boost::multiprecision::cpp_int toInt() const { // TODO: fake solution
        return front();
    }
    boost::rational<boost::multiprecision::cpp_int> to_rational() const { // TODO: fake solution
        if (back() < 0) {
            AUTOQ_ERROR("We assume the denominator should not be less than 1 here!");
            exit(1);
        }
        return boost::rational<boost::multiprecision::cpp_int>(front(), boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>(back()/2)));
    }
    std::string realToSMT() const {
        std::string result = "(/ (+ ";
        for (int i=0; i<N; i++)
            result += " (* " + std::to_string(std::cos(M_PI * i/N)) + " " + at(i).str() + ")";
        boost::multiprecision::cpp_int num = boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>(back()/2));
        if (back() % 2 == 0)
            result += ") " + num.str() + ")";
        else
            result += ") (* " + std::to_string(std::sqrt(2.0)) + " " + num.str() + ") )";
        return result;
    }
    std::string imagToSMT() const {
        std::string result = "(/ (+";
        for (int i=0; i<N; i++)
            result += " (* " + std::to_string(std::sin(M_PI * i/N)) + " " + at(i).str() + ")";
        boost::multiprecision::cpp_int num = boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>(back()/2));
        if (back() % 2 == 0)
            result += ") " + num.str() + ")";
        else
            result += ") (* " + std::to_string(std::sqrt(2.0)) + " " + num.str() + ") )";
        return result;
    }
    double abs2() const {
        double denominator = std::pow(std::sqrt(2.0), static_cast<double>(back()));
        double numerator_real = 0;
        for (int i=0; i<N; i++)
            numerator_real += std::cos(M_PI * i/N) * static_cast<double>(at(i));
        numerator_real /= denominator;
        double numerator_imag = 0;
        for (int i=0; i<N; i++)
            numerator_imag += std::sin(M_PI * i/N) * static_cast<double>(at(i));
        numerator_imag /= denominator;
        return numerator_real * numerator_real + numerator_imag * numerator_imag;
    }
    bool isZero() const {
        return std::all_of(this->begin(), std::prev(this->end()), [](auto item) { return item == 0; });
    }
    bool valueEqual(nTuple o) const {
        if (this->back() >= o.back()) {
            o.adjust_k(this->back() - o.back());
            return *this == o;
        } else {
            auto This = *this;
            This.adjust_k(o.back() - This.back());
            return This == o;
        }
    }
    nTuple& multiply_cos(const boost::rational<boost::multiprecision::cpp_int> &theta) {
        auto c1 = *this;
        auto c2 = *this;
        *this = (c1.counterclockwise(theta) + c2.counterclockwise(-theta)).divide_by_the_square_root_of_two(2);
        return *this;
    }
    nTuple& multiply_isin(const boost::rational<boost::multiprecision::cpp_int> &theta) {
        auto c1 = *this;
        auto c2 = *this;
        *this = (c1.counterclockwise(theta) - c2.counterclockwise(-theta)).divide_by_the_square_root_of_two(2);
        return *this;
    }

private:
    void adjust_k(boost::multiprecision::cpp_int dk) {
        if (dk < 0) {
            AUTOQ_ERROR("The parameter dk should not be less than 0!");
            exit(1);
        }
        while (dk > 0) {
            if (N < 4) {
                AUTOQ_ERROR("To do adjust_k, N should be at least 4.");
                exit(1);
            }
            nTuple ans;
            for (int i=0; i<=N-1; i++) {
                int targetAngle = i - N/4;
                boost::multiprecision::cpp_int targetAmplitude = this->at(i);
                while (targetAngle < 0) {
                    targetAngle += N;
                    targetAmplitude *= -1;
                }
                ans.at(targetAngle) += targetAmplitude;
                /*************************************/
                targetAngle = i + N/4;
                targetAmplitude = this->at(i);
                while (targetAngle >= N) {
                    targetAngle -= N;
                    targetAmplitude *= -1;
                }
                ans.at(targetAngle) += targetAmplitude;
            }
            ans.back() = this->back() + 1;
            *this = ans;
            dk--;
        }
    }
    nTuple binary_operation(const nTuple &o, bool add) const {
        assert(((back() == o.back()) ||
              (isZero() && back()<=o.back()) ||
              (o.isZero() && back()>=o.back())));// {
        //     AUTOQ_ERROR("The two nTuples should have the same k!");
        //     exit(1);
        // }
        nTuple symbol;
        for (int i=0; i<N; i++) {
            if (add) symbol.at(i) = at(i) + o.at(i);
            else symbol.at(i) = at(i) - o.at(i);
        }
        symbol.back() = std::max(back(), o.back()); // remember to set k
        return symbol;
    }
};

#endif