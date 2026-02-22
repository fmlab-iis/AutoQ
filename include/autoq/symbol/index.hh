#ifndef _AUTOQ_INDEX_HH_
#define _AUTOQ_INDEX_HH_

#include "autoq/symbol/symbol_base.hh"
#include <boost/functional/hash.hpp>
#include <autoq/autoq.hh>

namespace AUTOQ
{
	namespace Symbol
	{
        struct Index;
	}
}

struct AUTOQ::Symbol::Index : AUTOQ::Symbol::SymbolBase<Index> {
    int index;
    Index() : SymbolBase<Index>(false), index() {} // default: leaf (internal_ = false)
    Index(bool is_leaf_v, int idx) : SymbolBase<Index>(!is_leaf_v), index(idx) {} // internal_ = true when is_leaf_v is false

    int qubit() const {
        if (is_leaf()) {
            THROW_AUTOQ_ERROR("Leaf symbols do not have qubit().");
        }
        return index;
    }
    bool operator==(const Index &o) const { return is_leaf() == o.is_leaf() && index == o.index; }
    bool operator<(const Index &o) const {
        if (is_internal() && !o.is_internal()) return true;
        if (o.is_internal() && !is_internal()) return false;
        return index < o.index;
    }
    friend std::ostream& operator<<(std::ostream& os, const Index& obj) {
        if (obj.is_internal())
            os << "[" + std::to_string(obj.qubit()) + "]";
        else
            os << obj.index;
        return os;
    }
    std::string str() const {
        std::stringstream ss;
        ss << *this; // simply employ the above operator<<
        return ss.str();
    }
};

namespace boost {
    template <> struct hash<AUTOQ::Symbol::Index> {
        size_t operator()(const AUTOQ::Symbol::Index& obj) const {
            std::size_t seed = 0;
            boost::hash_combine(seed, obj.is_internal());
            boost::hash_combine(seed, obj.index);
            return seed;
        }
    };
}

#endif