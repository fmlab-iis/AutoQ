#ifndef _AUTOQ_NTUPLE_HH_
#define _AUTOQ_NTUPLE_HH_

#include <cmath>
#include <algorithm>
#include <boost/rational.hpp>
#include <autoq/util/convert.hh>
#include <autoq/util/mapped_vector.hh>
#include <boost/integer/common_factor.hpp>
#include <boost/multiprecision/cpp_int.hpp>

namespace AUTOQ
{
	namespace Complex
	{
        struct nTuple;
	}
}

struct AUTOQ::Complex::nTuple : AUTOQ::Util::mapped_vector<boost::multiprecision::cpp_int> {
    inline static long long N = 4; // the smallest angle unit = pi / N. Notice that N >= 4 if adjust_k is to be executed.
    boost::multiprecision::cpp_int k = 0;
    // Notice that if we do not use is_convertible_v, type int will not be accepted in this case.
    template <typename T>
        nTuple(T in) {
            k = 0;
            if constexpr(std::is_convertible<T, boost::rational<boost::multiprecision::cpp_int>>::value) {
                boost::rational<boost::multiprecision::cpp_int> r = in;
                auto d = r.denominator();
                while (d > 0 && d % 2 == 0) {
                    k += 2;
                    d >>= 1;
                }
                if (d != 1) { // Assume the denominator is a power of 2!
                    AUTOQ_ERROR("The denominator is not a power of 2!");
                    exit(1);
                }
                // The above just transform the denominator d into √2^back().
                const auto &x = r.numerator();
                if (x != 0)
                    operator[](0) = x;
            } else {
                AUTOQ_ERROR(in << " cannot be converted to a complex number!");
                exit(1);
            }
        }
    nTuple() : nTuple(0) {}
    static nTuple Angle(const boost::rational<boost::multiprecision::cpp_int> &theta) {
        return nTuple(1).counterclockwise(theta);
    }
    static nTuple One() { return nTuple(1); }
    static nTuple Zero() { return nTuple(0); }
    static nTuple Rand() {
        auto number = nTuple(0);
        auto val = rand() % 5;
        if (val != 0)
            number[rand() % N] = val;
        return number;
    }
    static nTuple sqrt2() { return nTuple(1).divide_by_the_square_root_of_two(-1); }
    friend std::ostream& operator<<(std::ostream& os, const nTuple& obj) {
        os << "[";
        for (const auto &kv : obj)
            os << " " << kv.second << "*eipi(" << kv.first << "/" << N << ")";
        os << "]";
        return os;
    }
    nTuple operator+(const nTuple &o) const { return binary_operation(o, true); }
    nTuple operator-(const nTuple &o) const { return binary_operation(o, false); }
    nTuple operator*(const nTuple &o) const {
        nTuple symbol;
        for (const auto &kv1 : *this) {
            for (const auto &kv2 : o) {
                auto targetAngle = kv1.first + kv2.first;
                boost::multiprecision::cpp_int targetAmplitude = kv1.second * kv2.second;
                while (targetAngle >= N) {
                    targetAngle -= N;
                    targetAmplitude = -targetAmplitude;
                }
                symbol[targetAngle] += targetAmplitude;
                if (symbol[targetAngle] == 0)
                    symbol.erase(targetAngle);
            }
        }
        symbol.k = this->k + o.k; // remember to set k
        return symbol;
    }
    nTuple operator/(nTuple denominator) const {
        auto numerator = *this;
        int grid = 1;
        // std::cout << AUTOQ::Util::Convert::ToString(numerator) << std::endl;
        // std::cout << AUTOQ::Util::Convert::ToString(denominator) << std::endl;
        while (!std::all_of(denominator.begin(), denominator.end(), [](const auto &kv) { return kv.first == 0 || kv.second == 0; })) {
            auto temp = denominator;
            for (auto &kv : temp) {
                if (kv.first % grid == 0 && (kv.first / grid) % 2 == 1)
                    kv.second *= -1;
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
        numerator.k -= denominator.k;
        denominator.k = 0;
        if (denominator.find(0) == denominator.end()) {
            AUTOQ_ERROR("The denominator should not be zero!");
            exit(1);
        }
        while (denominator[0] % 2 == 0) {
            denominator[0] >>= 1;
            numerator.k += 2;
        }
        if (std::all_of(numerator.begin(), numerator.end(), [&denominator](const auto &kv) mutable { return kv.second % denominator[0] == 0; })) {
            std::for_each(numerator.begin(), numerator.end(), [&denominator](auto &kv) mutable { kv.second /= denominator[0]; });
            // numerator.fraction_simplification();
            return numerator;
        } else {
            AUTOQ_ERROR("The result is not expressible!");
            exit(1);
        }
    }
    nTuple& fraction_simplification() { // TODO: still necessary for inclusion checking
        if (isZero()) k = 0;
        else {
            if (k < 0) {
                int dk2 = (1 + static_cast<int>(-k))/2;
                std::for_each(begin(), end(), [dk2](auto &kv) { kv.second *= boost::multiprecision::pow(boost::multiprecision::cpp_int(2), dk2); });
                k += dk2 * 2;
            }
            while (std::all_of(begin(), end(), [](const auto &kv) { return (kv.second & 1) == 0; }) && k >= 2) {
                std::for_each(begin(), end(), [](auto &kv) { kv.second >>= 1; });
                k -= 2;
            }
        }
        return *this;
    }
    nTuple& divide_by_the_square_root_of_two(int times=1) {
        k += times;
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
            AUTOQ_ERROR("This angle (" << theta << ") is not supported under N = " << N << ".");
            exit(1);
        }
        auto t = static_cast<long long>(N*2 * theta.numerator() / theta.denominator());
        // Solve theta = t / (N*2).
        nTuple result;
        for (const auto &kv : *this) {
            auto targetAngle = kv.first + t;
            auto targetAmplitude = kv.second;
            while (targetAngle >= N) {
                targetAngle -= N;
                targetAmplitude *= -1;
            }
            result[targetAngle] += targetAmplitude;
            if (result[targetAngle] == 0)
                result.erase(targetAngle);
        }
        result.k = k;
        *this = result;
        return *this;
    }
    boost::multiprecision::cpp_int toInt() const { // TODO: fake solution
        return at0();
    }
    boost::rational<boost::multiprecision::cpp_int> to_rational() const { // TODO: fake solution
        if (k < 0) {
            AUTOQ_ERROR("We assume the denominator should not be less than 1 here!");
            exit(1);
        }
        return boost::rational<boost::multiprecision::cpp_int>(at0(), boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>(k/2)));
    }
    std::string realToSMT() const {
        std::string result = "(/ (+ ";
        if (empty()) {
            result += " 0";
        } else {
            for (const auto &kv : *this)
                result += " (* " + std::to_string(std::cos(M_PI * kv.first/N)) + " " + kv.second.str() + ")";
        }
        boost::multiprecision::cpp_int num = boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>(k/2));
        if (k % 2 == 0)
            result += ") " + num.str() + ")";
        else
            result += ") (* " + std::to_string(std::sqrt(2.0)) + " " + num.str() + ") )";
        return result;
    }
    std::string imagToSMT() const {
        std::string result = "(/ (+";
        if (empty()) {
            result += " 0";
        } else {
            for (const auto &kv : *this)
                result += " (* " + std::to_string(std::sin(M_PI * kv.first/N)) + " " + kv.second.str() + ")";
        }
        boost::multiprecision::cpp_int num = boost::multiprecision::pow(boost::multiprecision::cpp_int(2), static_cast<int>(k/2));
        if (k % 2 == 0)
            result += ") " + num.str() + ")";
        else
            result += ") (* " + std::to_string(std::sqrt(2.0)) + " " + num.str() + ") )";
        return result;
    }
    double abs2() const {
        double denominator = std::pow(std::sqrt(2.0), static_cast<double>(k));
        double numerator_real = 0;
        for (const auto &kv : *this)
            numerator_real += std::cos(M_PI * kv.first/N) * static_cast<double>(kv.second);
        numerator_real /= denominator;
        double numerator_imag = 0;
        for (const auto &kv : *this)
            numerator_imag += std::sin(M_PI * kv.first/N) * static_cast<double>(kv.second);
        numerator_imag /= denominator;
        return numerator_real * numerator_real + numerator_imag * numerator_imag;
    }
    bool isZero() const {
        return std::all_of(begin(), end(), [](const auto &kv) { return kv.second == 0; });
    }
    bool valueEqual(nTuple o) const {
        if (k >= o.k) {
            o.adjust_k(k - o.k);
            return *this == o;
        } else {
            auto This = *this;
            This.adjust_k(o.k - This.k);
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
    bool operator==(const auto &rhs) const {
        return k == rhs.k && AUTOQ::Util::mapped_vector<boost::multiprecision::cpp_int>::operator==(rhs);
    }
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
            for (const auto &kv : *this) {
                long long targetAngle = kv.first - N/4;
                boost::multiprecision::cpp_int targetAmplitude = kv.second;
                while (targetAngle < 0) {
                    targetAngle += N;
                    targetAmplitude *= -1;
                }
                ans[targetAngle] += targetAmplitude;
                if (ans[targetAngle] == 0)
                    ans.erase(targetAngle);
                /*************************************/
                targetAngle = kv.first + N/4;
                targetAmplitude = kv.second;
                while (targetAngle >= N) {
                    targetAngle -= N;
                    targetAmplitude *= -1;
                }
                ans[targetAngle] += targetAmplitude;
                if (ans[targetAngle] == 0)
                    ans.erase(targetAngle);
            }
            ans.k = k + 1;
            *this = ans;
            dk--;
        }
    }
    nTuple real() const {
        nTuple result;
        for (const auto &kv : *this) {
            if (kv.first == 0) {
                result[0] += 2 * kv.second;
                if (result[0] == 0)
                    result.erase(0);
            } else {
                result[kv.first] += kv.second;
                if (result[kv.first] == 0)
                    result.erase(kv.first);
                result[N-kv.first] -= kv.second;
                if (result[N-kv.first] == 0)
                    result.erase(N-kv.first);
            }
        }
        result.k = this->k + 2;
        return result;
    }
    nTuple imag() const {
        nTuple result;
        for (const auto &kv : *this) {
            if (kv.first > 0) {
                result[kv.first] += kv.second;
                if (result[kv.first] == 0)
                    result.erase(kv.first);
                result[N-kv.first] += kv.second;
                if (result[N-kv.first] == 0)
                    result.erase(N-kv.first);
            }
        }
        result.k = this->k + 2;
        return result;
    }

private:
    nTuple binary_operation(const nTuple &o, bool add) const {
        assert(((k == o.k) ||
              (isZero() && k<=o.k) ||
              (o.isZero() && k>=o.k)));// {
        //     AUTOQ_ERROR("The two nTuples should have the same k!");
        //     exit(1);
        // }
        nTuple result = *this;
        for (const auto &kv : o) {
            if (add) result[kv.first] = result[kv.first] + kv.second;
            else result[kv.first] = result[kv.first] - kv.second;
            if (result[kv.first] == 0)
                result.erase(kv.first);
        }
        result.k = std::max(k, o.k); // remember to set k
        return result;
    }
};

#endif