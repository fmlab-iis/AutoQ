#ifndef _AUTOQ_MAPPED_VECTOR_HH_
#define _AUTOQ_MAPPED_VECTOR_HH_

#include <map>

namespace AUTOQ
{
	namespace Util
	{
		template <typename T>
		struct mapped_vector;
	}
}

template <typename T>
struct AUTOQ::Util::mapped_vector : std::map<long long, T>
{
    T at0() const {
        const auto &it = this->find(0);
        if (it == this->end())
            return T();
        return it->second;
    }

	inline bool operator==(const mapped_vector& rhs2) const
	{
        std::map<long long, T> lhs = *this;
        for (const auto &kv : *this) {
            if (kv.second == 0) {
                lhs.erase(kv.first);
            }
        }
        std::map<long long, T> rhs = rhs2;
        for (const auto &kv : rhs2) {
            if (kv.second == 0) {
                rhs.erase(kv.first);
            }
        }
		return lhs == rhs;
	}
};

#endif