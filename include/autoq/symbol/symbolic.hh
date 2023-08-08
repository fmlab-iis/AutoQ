#ifndef _AUTOQ_SYMBOLIC_HH_
#define _AUTOQ_SYMBOLIC_HH_

#include <vector>
#include <autoq/util/convert.hh>
#include <boost/multiprecision/cpp_int.hpp>

namespace AUTOQ
{
	namespace Symbol
	{
        struct linear_combination;
        struct Symbolic;
	}
}

// Symbolic symbol
typedef std::map<std::string, boost::multiprecision::cpp_int> stdmapstdstringboostmultiprecisioncpp_int;
struct AUTOQ::Symbol::linear_combination : std::map<std::string, boost::multiprecision::cpp_int> {
    using stdmapstdstringboostmultiprecisioncpp_int::stdmapstdstringboostmultiprecisioncpp_int;
    linear_combination operator+(linear_combination b) const {
        for (const auto &kv : *this) {
            auto k = kv.first;
            auto v = kv.second;
            b[k] += v;
        }
        return b;
    }
    linear_combination operator-(const linear_combination &b) const {
        auto a = *this; // copy!
        for (const auto &kv : b) {
            auto k = kv.first;
            auto v = kv.second;
            a[k] -= v;
        }
        return a;
    }
    linear_combination operator*(const linear_combination &b) const {
        linear_combination ans;
        for (const auto &kv1 : *this) {
            for (const auto &kv2 : b) {
                if (kv1.first == "1") {
                    ans[kv2.first] += kv1.second * kv2.second;
                } else if (kv2.first == "1") {
                    ans[kv1.first] += kv1.second * kv2.second;
                } else if (kv1.first < kv2.first) {
                    ans[kv1.first + "*" + kv2.first] += kv1.second * kv2.second;
                } else {
                    ans[kv2.first + "*" + kv1.first] += kv1.second * kv2.second;
                }
            }
        }
        return ans;
    }
    friend std::ostream& operator<<(std::ostream& os, const linear_combination& obj) {
        // os << AUTOQ::Util::Convert::ToString(static_cast<stdmapstdstringboostmultiprecisioncpp_int>(obj));
        if (obj.empty()) {
            os << "0";
            return os;
        }
        for (auto kv = obj.begin(); kv != obj.end(); ++kv) {
            if (kv->first == "1")
                os << kv->second;
            else {
                if (kv->second != 1)
                    os << kv->second;
                os << kv->first;
            }
            if (std::next(kv) != obj.end())
                os << ' ';
        }
        return os;
    }
};
typedef std::vector<AUTOQ::Symbol::linear_combination> stdvectorstdmapstdstringboostmultiprecisioncpp_int;
struct AUTOQ::Symbol::Symbolic : stdvectorstdmapstdstringboostmultiprecisioncpp_int {
    using stdvectorstdmapstdstringboostmultiprecisioncpp_int::stdvectorstdmapstdstringboostmultiprecisioncpp_int;
    typedef typename AUTOQ::Symbol::Symbolic::value_type Map;
    typedef typename AUTOQ::Symbol::Symbolic::value_type::value_type Pair;
    typedef typename AUTOQ::Symbol::Symbolic::value_type::mapped_type Entry;
    template <typename T, typename = std::enable_if_t<std::is_convertible<T, Entry>::value>>
        Symbolic(T qubit) : stdvectorstdmapstdstringboostmultiprecisioncpp_int({Map{{"1", qubit}}}) {}
    Entry qubit() const { return is_internal() ? at(0).at("1") : 0; }
    Entry k() const { 
        if (is_internal()) return -1;
        if (at(4).empty()) return 0;
        auto ptr = at(4).find("1");
        if (ptr == at(4).end()) {
            throw std::runtime_error("[ERROR] Each k must be a constant!");
        } else {
            return ptr->second;
        }
    }
    bool is_leaf() const { return size() == 5; }
    bool is_internal() const { return size() < 5; }
    void back_to_zero() {
        std::fill(begin(), begin()+4, Map());
    }
    friend std::ostream& operator<<(std::ostream& os, const Symbolic& obj) {
        os << AUTOQ::Util::Convert::ToString(static_cast<stdvectorstdmapstdstringboostmultiprecisioncpp_int>(obj));
        return os;
    }
    Symbolic operator+(const Symbolic &o) const { return binary_operation(o, true); }
    Symbolic operator-(const Symbolic &o) const { return binary_operation(o, false); }
    Symbolic binary_operation(Symbolic o, bool add) const {
        assert(this->at(4) == o.at(4)); // Two k's must be the same.
        Symbolic symbol;
        for (int i=0; i<4; i++) { // We do not change k here.
            if (add)
                symbol.push_back(at(i) + o.at(i));
            else
                symbol.push_back(at(i) - o.at(i));
        }
        symbol.push_back(this->at(4)); // remember to push k
        return symbol;
    }
    Symbolic operator*(const Symbolic &o) const {
        Symbolic symbol;
        symbol.push_back(at(0)*o.at(0) - at(1)*o.at(3) - at(2)*o.at(2) - at(3)*o.at(1));
        symbol.push_back(at(0)*o.at(1) + at(1)*o.at(0) - at(2)*o.at(3) - at(3)*o.at(2));
        symbol.push_back(at(0)*o.at(2) + at(1)*o.at(1) + at(2)*o.at(0) - at(3)*o.at(3));
        symbol.push_back(at(0)*o.at(3) + at(1)*o.at(2) + at(2)*o.at(1) + at(3)*o.at(0));
        symbol.push_back(at(4) + o.at(4)); // remember to push k
        return symbol;
    }
    void fraction_simplification() {
        while (std::all_of(begin(), begin()+4, [](const Map &m) {
            return std::all_of(m.begin(), m.end(), [](const auto &p) { return (p.second&1)==0; });
        }) && at(4).find("1")!=at(4).end() && at(4).at("1") >= 2) { // Notice the parentheses enclosing i&1 are very important!
            for (int i=0; i<4; i++) {
                std::for_each(at(i).begin(), at(i).end(), [](auto &p) { p.second /= 2; });
                for (auto it = at(i).begin(); it != at(i).end(); )
                    if (it->second == 0)
                        it = at(i).erase(it);
                    else
                        ++it;
            }
            at(4).at("1") -= 2;
        }
        if (std::all_of(begin(), begin()+4, [](const Map &m) { return m.empty(); }))
            at(4).clear();
    }
    void omega_multiplication(int rotation=1) {
        int r = rotation;
        while (r != 0) {
            if (r > 0) {
                auto temp = at(3);
                for (int i=3; i>=1; i--) { // exclude "k"
                    at(i) = at(i-1);
                }
                std::for_each(temp.begin(), temp.end(), [](auto &p) { p.second = -p.second; });
                at(0) = temp;
                r--;
            } else {
                auto temp = at(0);
                for (int i=0; i<=2; i++) { // exclude "k"
                    at(i) = at(i+1);
                }
                std::for_each(temp.begin(), temp.end(), [](auto &p) { p.second = -p.second; });
                at(3) = temp;
                r++;
            }
        }
    }
    void divide_by_the_square_root_of_two() {
        at(4)["1"]++; // use [] instead of () in case the original map is empty.
    }
    void negate() {
        for (int i=0; i<4; i++)
            std::for_each(at(i).begin(), at(i).end(), [](auto &p) { p.second = -p.second; });
    }
    void degree45cw() {
        auto t = at(0);
        for (int i=0; i<3; i++) {
            at(i) = at(i+1);
        }
        std::for_each(t.begin(), t.end(), [](auto &p) { p.second = -p.second; });
        at(3) = t;
    }
    void degree90cw() {
        auto a=at(2), b=at(3), c=at(0), d=at(1);
        at(0)=a; at(1)=b;
        std::for_each(c.begin(), c.end(), [](auto &p) { p.second = -p.second; });
        at(2)=c;
        std::for_each(d.begin(), d.end(), [](auto &p) { p.second = -p.second; });
        at(3)=d;
    }
};

#endif