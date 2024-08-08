#ifndef _AUTOQ_INDEX_HH_
#define _AUTOQ_INDEX_HH_

#include <boost/functional/hash.hpp>
#include <autoq/autoq.hh>

namespace AUTOQ
{
	namespace Symbol
	{
        struct Index;
	}
}

struct AUTOQ::Symbol::Index {
    int index;
    bool is_leaf_v = true;
    Index() : index(), is_leaf_v() {} // prevent the compiler from complaining about the lack of default constructor
    Index(bool is_leaf_v, int index) : index(index), is_leaf_v(is_leaf_v) {}
    bool is_leaf() const { return is_leaf_v; }
    bool is_internal() const { return !is_leaf_v; }
    int qubit() const {
        if (is_leaf_v) {
            AUTOQ_ERROR("Leaf symbols do not have qubit().");
            exit(1);
        }
        return index;
    }
    bool operator==(const Index &o) const { return is_leaf_v == o.is_leaf_v && index == o.index; }
    bool operator<(const Index &o) const {
        if (is_leaf_v && !o.is_leaf_v) return false;
        if (o.is_leaf_v && !is_leaf_v) return true;
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