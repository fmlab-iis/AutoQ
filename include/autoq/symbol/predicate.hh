#ifndef _AUTOQ_PREDICATE_HH_
#define _AUTOQ_PREDICATE_HH_

#include <string>
#include "autoq/symbol/symbol_base.hh"
#include "autoq/autoq.hh"
#include <boost/multiprecision/cpp_int.hpp>

namespace AUTOQ
{
	namespace Symbol
	{
        struct Predicate;
	}
}

struct AUTOQ::Symbol::Predicate : std::string, AUTOQ::Symbol::SymbolBase<Predicate> {
    using std::string::string;
    inline static std::map<std::pair<Predicate, Predicate>, Predicate> mulmap;
    Predicate(const std::string& str) : std::string(str), SymbolBase<Predicate>(false) {} // leaf: internal_ = false
    template <typename T, typename = std::enable_if_t<std::is_convertible<T, boost::multiprecision::cpp_int>::value>>
    Predicate(T qubit) : std::string(static_cast<boost::multiprecision::cpp_int>(qubit).str()), SymbolBase<Predicate>(true) {} // internal

    boost::multiprecision::cpp_int qubit() const {
        if (is_leaf()) {
            THROW_AUTOQ_ERROR("Leaf symbols do not have qubit().");
        }
        return boost::multiprecision::cpp_int(*this);
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
        return static_cast<const std::string&>(*this) < static_cast<const std::string&>(o);
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