#ifndef _AUTOQ_NTUPLE_HH_
#define _AUTOQ_NTUPLE_HH_

#include <boost/functional/hash.hpp>
#include <boost/multiprecision/cpp_int.hpp>
#include <boost/rational.hpp>
#include <cmath>
#include <iostream>

namespace AUTOQ {
    namespace Complex {
        struct nTuple;
    }
}

typedef boost::rational<boost::multiprecision::cpp_int> rational;

struct AUTOQ::Complex::nTuple {

private:
    const inline static int N = 4; // the cyclomotic polynomial has highest degree of N
    rational coeff[2 * N];
    rational operator[](int idx) const {
        return coeff[idx];
    }
    int deg() const {
        int d = 0;
        for (int i = 0; i < 2 * N; i++) {
            if (coeff[i].numerator() != 0) {
                d = i;
            }
        }
        return d;
    }
    void set(const rational &a, int d) {
        if (d > N) {
            throw std::runtime_error("invalid power");
        } else {
            coeff[d] = a;
        }
    }

public:
    template <typename T, typename = std::enable_if_t<std::is_convertible<T, rational>::value>>
    nTuple(T in) {
        // deg = 0;
        // for (int i = 0; i < 2 * N; i++) {
        //     coeff[i].numerator = 0;
        //     coeff[i].denominator = 1;
        // }
    }
    nTuple() {
        for (int i = 0; i < 2 * N; i++) {
            coeff[i] = 0;
        }
    }
    static nTuple Angle(rational r) {
        r -= r.numerator() / r.denominator();
        while (r >= 1)
            r -= 1;
        while (r < 0)
            r += 1;
        nTuple p;
        if (N % r.denominator() != 0) {
            throw std::runtime_error("Angle not supported!");
        } else {
            p.set(rational(1), static_cast<int>(N * r.numerator() / r.denominator()));
            return p;
        }
    }
    // void set_to_zeros() {
    //     for (int i = 0; i <= deg; i++) {
    //         coeff[i].numerator() = 0;
    //         coeff[i].denominator() = 1;
    //     }
    //     deg = update_degree();
    // }
    // void zero() {
    //     for (int i = 0; i <= deg; i++) {
    //         coeff[i].numerator = 0;
    //         coeff[i].denominator = 1;
    //     }
    //     deg = update_degree();
    // }
    // void one() {
    //     rational one(1);
    //     Zero();
    //     set(one, 0);
    // }
    static nTuple One() {
        nTuple p;
        p.set(rational(1), 0);
        return p;
    }
    static nTuple Zero() {
        return nTuple(2);
    }
    static nTuple Rand() {
        nTuple p;
        for (size_t i = 0; i < N; i++) {
            rational tmp((rand() - 2147483646 / 2) % 10000, (rand() + 1) % 100000);
            p.set(tmp, i);
        }
        return p;
    }
    static nTuple sqrt2() { // TODO: for nTuple now only when N=4
        nTuple p;
        p.set(rational(1), 1);
        p.set(rational(-1), 3);
        return p;
    }
    // void show() {
    //     for (int i = this->deg; i >= 0; i--) {
    //         this->coeff[i].show();
    //         std::cout << "x^" << i;
    //         if (i > 0) {
    //             std::cout << "+";
    //         }
    //     }
    //     std::cout << std::endl;
    // }
    friend std::ostream& operator<<(std::ostream &os, const nTuple &obj) {
        os << AUTOQ::Util::Convert::ToString(std::vector<rational>(std::begin(obj.coeff), std::end(obj.coeff)));
        return os;
    }

    // nTuple operator=(const nTuple &poly_b) {
    //     this->set_to_zeros();
    //     for (int i = 0; i <= max(poly_b.deg, this->deg); i++) {
    //         this->coeff[i] = poly_b.coeff[i];
    //     }
    //     this->deg = poly_b.deg;
    //     return *this;
    // }

    nTuple operator+(const nTuple &poly_b) const {
        nTuple result;
        auto deg = std::max(poly_b.deg(), this->deg());
        for (int i = 0; i <= deg; i++) {
            result.coeff[i] = this->coeff[i] + poly_b.coeff[i];
        }
        return result;
    }

    nTuple operator-(const nTuple &poly_b) const {
        nTuple result;
        auto deg = std::max(poly_b.deg(), this->deg());
        for (int i = 0; i <= deg; i++) {
            result.coeff[i] = this->coeff[i] - poly_b.coeff[i];
        }
        return result;
    }
    // nTuple operator*(const rational &r) {
    //     nTuple tmp(0);
    //     for (int i = 0; i <= this->deg; i++) {
    //         tmp.coeff[i] = this->coeff[i] * r;
    //     }
    //     tmp.update_degree();
    //     return tmp;
    // }
    nTuple operator*(const nTuple &poly_b) const {
        nTuple tmp;
        auto deg = this->deg() + poly_b.deg();
        for (int i = 0; i <= deg; i++) {
            for (int j = 0; j <= i; j++) {
                tmp.coeff[i] += this->coeff[j] * poly_b[i - j];
            }
        }
        // std::cout<<tmp.deg <<std::endl;
        // tmp.show();
        nTuple cyclo_poly;
        cyclo_poly.set(rational(1), 4);
        cyclo_poly.set(rational(1), 0);
        tmp = tmp / cyclo_poly;
        // std::cout<<tmp.deg <<std::endl;
        // cyclo_poly.show();
        // tmp.show();

        return tmp;
    }

    nTuple operator/(const nTuple &poly_b) const {
        int tmp_deg;
        nTuple tmp = *this;
        auto poly_b_deg = poly_b.deg();
        while ((tmp_deg=tmp.deg()) >= poly_b_deg) {
            rational r = tmp.coeff[tmp_deg] / poly_b[poly_b_deg];
            for (int i = poly_b_deg; i >= 0; i--) {
                tmp.coeff[tmp_deg - i] = tmp.coeff[tmp_deg - i] - (r * poly_b[poly_b_deg - i]);
                // rational t = this->coeff[tmp.deg - i] - (r * poly_b[poly_b.deg - i]);
            }
        }
        return tmp;
    }
    // nTuple operator/(rational &r) {
    //     for (int i = 0; i <= this->deg; i++) {
    //         this->coeff[i] = this->coeff[i] / r;
    //     }
    //     this->update_degree();
    //     return *this;
    // }
    nTuple& fraction_simplification() {
        return *this;
    }
    nTuple& divide_by_the_square_root_of_two(int times = 1) {
        nTuple var = sqrt2();
        while (times--) {
            *this = *this / var;
        }
        return *this;
    }
    nTuple& counterclockwise(const rational &r) {
        *this = nTuple::operator*(nTuple::Angle(r));
        return *this;
        // nTuple tmp = nTuple(0).Angle(r);
        // *this = *this * tmp;
        // return *this;
    }
    nTuple& clockwise(const rational &r) {
        *this = nTuple::operator*(nTuple::Angle(-r));
        return *this;
        // rational minus_one(-1, 1);
        // rational one(1, 1);
        // *this = *this * minus_one;
        // rational tmp = one - r;
        // this->counterclockwise(tmp);
        // return *this;
    }
    boost::multiprecision::cpp_int toInt() const {
        if (this->deg() == 0 && this->coeff[0].denominator() == 1) {
            return this->coeff[0].numerator();
        } else {
            std::cout << "this is not a int" << std::endl;
            return 0;
        }
    }
    rational to_rational() const {
        auto deg = this->deg();
        if (deg == 0) {
            return coeff[0];
        } else {
            std::cout << "this is not a rational " << std::endl;
            return coeff[deg + 1]; // arbitrary value?
        }
    }
    std::string realToSMT() const {
        double re = 0;
        auto deg = this->deg();
        for (int i = 0; i <= deg; i++) {
            double tmp = static_cast<double>(this->coeff[i].numerator()) / static_cast<double>(this->coeff[i].denominator());
            re += tmp * cos(i * M_PI / N);
        }
        return std::to_string(re);
    }
    std::string imagToSMT() const {
        double im = 0;
        auto deg = this->deg();
        for (int i = 0; i <= deg; i++) {
            double tmp = static_cast<double>(this->coeff[i].numerator()) / static_cast<double>(this->coeff[i].denominator());
            im += tmp * sin(i * M_PI / N);
        }
        return std::to_string(im);
    }
    double abs2() const {
        double re, im;
        re = 0;
        im = 0;
        auto deg = this->deg();
        for (int i = 0; i <= deg; i++) {
            double tmp = static_cast<double>(this->coeff[i].numerator()) / static_cast<double>(this->coeff[i].denominator());
            // std::cout << "n and d are " << this->coeff[i].numerator() << " " << this->coeff[i].denominator() << std::endl;
            // std::cout << "tmp is " << tmp << std::endl;
            re += tmp * cos(i * M_PI / N);
            im += tmp * sin(i * M_PI / N);
        }
        // std::cout << "re is" << re << std::endl;
        // std::cout << "im is " << im << std::endl;
        return (re * re + im * im);
    }
    bool operator==(const nTuple &poly_b) const {
        auto this_deg = this->deg();
        if (this_deg == poly_b.deg()) {
            for (int i = 0; i <= this_deg; i++) {
                if (this->coeff[i] != poly_b.coeff[i]) {
                    return false;
                }
            }
        }
        return true;
    }
    bool operator<(const nTuple &poly_b) const {
        auto this_deg = this->deg();
        auto poly_b_deg = poly_b.deg();
        if (this_deg < poly_b_deg)
            return true;
        else if (this_deg > poly_b_deg)
            return false;
        else {
            for (int i = this_deg; i >= 0; i--) {
                if (this->coeff[i] != poly_b.coeff[i]) {
                    return this->coeff[i] < poly_b.coeff[i];
                }
            }
            return false; // equal
        }
    }
    bool isZero() const {
        return (this->deg() == 0 && this->coeff[0].numerator() == 0);
    }

    // Define hash_value function for nTuple
    friend std::size_t hash_value(const nTuple& nt) {
        std::size_t seed = 0;
        // Combine hash values of individual members using boost::hash_combine
        for (size_t i = 0; i < 2 * N; i++) {
            boost::hash_combine(seed, nt.coeff[i]);
        }
        return seed;
    }
};

#endif
