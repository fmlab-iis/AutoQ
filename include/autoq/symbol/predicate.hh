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
    inline static std::map<std::pair<Predicate, Predicate>, Predicate> mulmap;
    Predicate(const std::string& str) : std::string(str) {} // Constructor accepting std::string
    template <typename T, typename = std::enable_if_t<std::is_convertible<T, boost::multiprecision::cpp_int>::value>>
        Predicate(T qubit) : std::string(static_cast<boost::multiprecision::cpp_int>(qubit).str()) { is_leaf_v = false; }
    // boost::multiprecision::cpp_int k() const { return 0; } // for complying with the other two types in parse_timbuk
    bool is_leaf() const { return is_leaf_v; }
    bool is_internal() const { return !is_leaf_v; }
    boost::multiprecision::cpp_int qubit() const {
        if (is_leaf_v) {
            THROW_AUTOQ_ERROR("Leaf symbols do not have qubit().");
        }
        return boost::multiprecision::cpp_int(std::stoi(*this));
    }
    Predicate operator*(const Predicate &o) const { // actually performs "or" operation
        if (!mulmap.empty()) {
            auto it = mulmap.find(std::make_pair(*this, o));
            if (it != mulmap.end()) return it->second;
            // it = mulmap.find(std::make_pair(o, *this));
            // if (it != mulmap.end()) return it->second;
        }
        if (*this == "false") return o;
        if (o == "false") return *this;
        if (*this == "true" || o == "true") return "true";
        return Predicate(std::string("(or " + *this + " " + o + ")").c_str());
    }
    std::string str() const {
        return *this;
    }
    bool operator<(const Predicate &o) const {
        if (is_internal() && !o.is_internal()) return true;
        if (o.is_internal() && !is_internal()) return false;
        if (is_internal() && o.is_internal()) return std::stoi(*this) < std::stoi(o);
        return std::string(*this) < std::string(o);
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