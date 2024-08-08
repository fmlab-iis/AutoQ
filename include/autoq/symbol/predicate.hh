#ifndef _AUTOQ_PREDICATE_HH_
#define _AUTOQ_PREDICATE_HH_

#include <string>
#include <autoq/autoq.hh>
#include <boost/multiprecision/cpp_int.hpp>

namespace AUTOQ
{
	namespace Symbol
	{
        struct Predicate;
	}
}

struct AUTOQ::Symbol::Predicate : std::string {
    using std::string::string;
    bool is_leaf_v = true;
    template <typename T, typename = std::enable_if_t<std::is_convertible<T, boost::multiprecision::cpp_int>::value>>
        Predicate(T qubit) : std::string(static_cast<boost::multiprecision::cpp_int>(qubit).str()) { is_leaf_v = false; }
    // boost::multiprecision::cpp_int k() const { return 0; } // for complying with the other two types in parse_timbuk
    bool is_leaf() const { return is_leaf_v; }
    bool is_internal() const { return !is_leaf_v; }
    boost::multiprecision::cpp_int qubit() const {
        if (is_leaf_v) {
            AUTOQ_ERROR("Leaf symbols do not have qubit().");
            exit(1);
        }
        return boost::multiprecision::cpp_int(std::stoi(*this));
    }
    Predicate operator*(const Predicate &o) const {
        if (*this == "true") return o;
        if (o == "true") return *this;
        if (*this == "false" || o == "false") return "false";
        return Predicate(std::string("(and " + *this + " " + o + ")").c_str());
    }
    std::string str() const {
        return *this;
    }
};

namespace boost {
    template <> struct hash<AUTOQ::Symbol::Predicate> {
        size_t operator()(const AUTOQ::Symbol::Predicate& obj) const {
            std::size_t seed = 0;
            boost::hash_combine(seed, obj.is_internal());
            boost::hash_combine(seed, obj.str());
            return seed;
        }
    };
}

#endif