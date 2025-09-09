#ifndef _AUTOQ_SYMBOLICCOMPLEX_HH_
#define _AUTOQ_SYMBOLICCOMPLEX_HH_

#include "autoq/util/convert.hh"
#include "autoq/complex/complex.hh"
#include <boost/multiprecision/cpp_int.hpp>

typedef boost::rational<boost::multiprecision::cpp_int> rational;

namespace AUTOQ {
	namespace Complex {
        struct SymbolicComplex;
        struct Term;
	}
}

// It is used for recording something like a^3 * b^2.
struct AUTOQ::Complex::Term : std::map<std::string, boost::multiprecision::cpp_int> {
    Term operator*(Term o) const {
        for (const auto &kv : *this) {
            o[kv.first] += kv.second;
            // if (o[kv.first] == 0)
            //     o.erase(kv.first);
        }
        return o;
    }
    static z3::expr mul(const std::vector<std::string> &v) {
        z3::context ctx;
        return mul(v, ctx);
    }
    static z3::expr mul(const std::vector<std::string> &v, z3::context &ctx) {
        if (v.size() == 1) {
            return ctx.real_const(v.at(0).c_str());
        }
        z3::expr_vector args(ctx);
        for (const auto &var : v) {
            args.push_back(ctx.real_const(var.c_str()));
        }
        assert(args.size() > 0);
        z3::array<Z3_ast> _args(args);
        Z3_ast r = Z3_mk_mul(ctx, _args.size(), _args.ptr());
        ctx.check_error();
        return z3::expr(ctx, r).simplify();
    }
    std::string expand() const {
        z3::context ctx;
        return expand(ctx).to_string();
    }
    z3::expr expand(z3::context &ctx) const { // can only be used in (* ...)
        if (empty()) return ctx.real_val("1");
        std::vector<std::string> vec;
        for (const auto &kv : *this) {
            const auto &s = kv.first;
            auto v = kv.second;
            if (v < 0) {
                THROW_AUTOQ_ERROR("We do not support negative powers.");
            }
            while (v > 0) {
                v--;
                vec.push_back(s);
            }
        }
        z3::expr result = mul(vec, ctx).simplify();
        return result;
    }
    friend std::ostream& operator<<(std::ostream& os, const Term& obj) {
        os << obj.expand();
        return os;
    }
};
struct AUTOQ::Complex::SymbolicComplex : std::map<Term, Complex> {
    static SymbolicComplex MySymbolicComplexConstructor(int i) {
        return MySymbolicComplexConstructor(Complex(i));
    }
    static SymbolicComplex MySymbolicComplexConstructor(const std::map<Term, Complex>& m) {
        SymbolicComplex sc;
        sc.insert(m.begin(), m.end());
        return sc;
    }
    static SymbolicComplex MySymbolicComplexConstructor(const Complex &c) {
        if (c.isZero()) return {}; // IMPORTANT: keep the keys nonzero to simplify the structure very much!
        SymbolicComplex result;
        result[Term()] = c;
        return result;
    }
    static SymbolicComplex MySymbolicComplexConstructor(const std::string &name) {
        std::set<std::string> vars;
        return MySymbolicComplexConstructor(name, vars);
    }
    static SymbolicComplex MySymbolicComplexConstructor(const std::string &name, std::set<std::string> &vars) {
        vars.insert(name + "R");
        vars.insert(name + "I");
        SymbolicComplex result;
        Term key; key[name + "R"] = 1;
        result[key] = Complex::One();
        key.clear(); key[name + "I"] = 1;
        result[key] = Complex::Angle(rational(2, 8));
        return result;
    }
    SymbolicComplex operator+(SymbolicComplex o) const {
        for (const auto &kv : *this) {
            o[kv.first] = o[kv.first] + kv.second;
            if (o[kv.first].isZero())
                o.erase(kv.first);
        }
        return o;
    }
    SymbolicComplex& operator+=(const SymbolicComplex &o) { *this = *this + o; return *this; }
    SymbolicComplex operator-(const SymbolicComplex &o) const {
        auto result = *this;
        for (const auto &kv : o) {
            result[kv.first] = result[kv.first] - kv.second;
            if (result[kv.first].isZero())
                result.erase(kv.first);
        }
        return result;
    }
    SymbolicComplex operator*(const SymbolicComplex &o) const {
        AUTOQ::Complex::SymbolicComplex result;
        std::set<Term> keys;
        for (const auto &kv1 : *this) {
            for (const auto &kv2 : o) {
                auto key = kv1.first * kv2.first;
                keys.insert(key);
                result[key] = result[key] + kv1.second * kv2.second;
            }
        }
        for (const auto &key : keys) {
            if (result.at(key).isZero())
                result.erase(key);
        }
        return result;
    }
    SymbolicComplex operator/(const Complex &o) const {
        AUTOQ::Complex::SymbolicComplex result;
        for (const auto &kv : *this) {
            result[kv.first] = kv.second / o;
        }
        return result;
    }
    SymbolicComplex operator*(int c) const {
        SymbolicComplex result;
        if (c != 0) {
            for (const auto &kv : *this) {
                result[kv.first] = kv.second * c;
            }
        }
        return result;
    }
    friend std::ostream& operator<<(std::ostream& os, const SymbolicComplex& obj) {
        bool isFirst = true;
        for (const auto &tc : static_cast<std::map<Term, Complex>>(obj)) {
            if (tc.second.isZero()) continue;
            if (!isFirst) os << " + ";
            if (tc.second != Complex(1) || tc.first.empty())
                os << tc.second;
            if (!tc.first.empty()) {
                if (tc.second != Complex(1))
                    os << " * ";
                os << tc.first;
            }
            isFirst = false;
        }
        if (obj.empty()) os << "0";
        return os;
    }
    std::string realToSMT() const {
        z3::context ctx;
        return realToSMT(ctx).to_string();
    }
    z3::expr realToSMT(z3::context &ctx) const {
        if (empty()) return ctx.real_val("0");
        z3::expr_vector ev(ctx);
        for (const auto &kv : *this) {
            auto k = kv.first;
            auto v = kv.second;
            ev.push_back(k.expand(ctx) *  v.realToSMT(ctx));
        }
        auto result = z3::sum(ev).simplify();
        return result;
    }
    SymbolicComplex real() const {
        SymbolicComplex result;
        for (const auto &kv : *this) {
            auto k = kv.first;
            auto v = kv.second.real();
            if (v.isZero()) continue;
            result[k] = v;
        }
        return result;
    }
    std::string imagToSMT() const {
        z3::context ctx;
        return imagToSMT(ctx).to_string();
    }
    z3::expr imagToSMT(z3::context &ctx) const {
        if (empty()) return ctx.real_val("0");
        z3::expr_vector ev(ctx);
        for (const auto &kv : *this) {
            auto k = kv.first;
            auto v = kv.second;
            ev.push_back(k.expand(ctx) *  v.imagToSMT(ctx));
        }
        auto result = z3::sum(ev).simplify();
        return result;
    }
    SymbolicComplex imag() const {
        SymbolicComplex result;
        for (const auto &kv : *this) {
            auto k = kv.first;
            auto v = kv.second.imag();
            if (v.isZero()) continue;
            result[k] = v;
        }
        return result;
    }
    void fraction_simplification() {
        for (auto &kv : *this) {
            kv.second.fraction_simplification();
        }
    }
    bool isConst() const {
        return empty() || (size() == 1 && begin()->first.empty());
    }
    rational to_rational() const {
        assert(isConst());
        if (empty()) return 0;
        return begin()->second.to_rational();
    }
    Complex to_complex() const {
        assert(isConst());
        if (empty()) return 0;
        return begin()->second;
    }
    boost::multiprecision::cpp_int max_k() const {
        boost::multiprecision::cpp_int k = INT_MIN;
        for (auto kv : *this) {
            if (k < kv.second.k())
                k = kv.second.k();
        }
        return k;
    }
    void adjust_k_and_discard(boost::multiprecision::cpp_int k) {
        fraction_simplification();
        for (auto &kv : *this) {
            auto &c = kv.second;
            while (c.k() < k)
                c.increase_k();
            c.k() = 0;
        }
    }
    std::set<std::string> vars() const {
        std::set<std::string> result;
        for (const auto &kv : *this) {
            for (const auto &kv2 : kv.first) {
                result.insert(kv2.first);
            }
        }
        return result;
    }
};

#endif
