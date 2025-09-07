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

	inline bool operator<(const mapped_vector& rhs2) const {
        return static_cast<std::map<long long, T>>(*this) < static_cast<std::map<long long, T>>(rhs2);
    }
    inline bool operator==(const mapped_vector& rhs2) const {
        return static_cast<std::map<long long, T>>(*this) == static_cast<std::map<long long, T>>(rhs2);
	}
};

#endif