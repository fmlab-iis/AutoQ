#ifndef _AUTOQ_FIVETUPLE_HH_
#define _AUTOQ_FIVETUPLE_HH_

#include <vector>
#include <autoq/util/convert.hh>
#include <boost/multiprecision/cpp_int.hpp>

namespace AUTOQ
{
	namespace Complex
	{
        struct FiveTuple;
	}
}

// Concrete symbol
typedef std::vector<boost::multiprecision::cpp_int> stdvectorboostmultiprecisioncpp_int;
struct AUTOQ::Complex::FiveTuple : stdvectorboostmultiprecisioncpp_int {
    using stdvectorboostmultiprecisioncpp_int::stdvectorboostmultiprecisioncpp_int;
    typedef typename AUTOQ::Complex::FiveTuple::value_type Entry;
    // Notice that if we do not use is_convertible_v, type int will not be accepted in this case.
    template <typename T, typename = std::enable_if_t<std::is_convertible<T, Entry>::value>>
        FiveTuple(T qubit) : stdvectorboostmultiprecisioncpp_int({qubit}) {} 
    static FiveTuple One() { return FiveTuple({1,0,0,0,0}); }
    static FiveTuple Zero() { return FiveTuple({0,0,0,0,0}); }
    static FiveTuple Rand() { return FiveTuple({rand()%5, rand()%5, rand()%5, rand()%5, 0}); }
    Entry qubit() const { return is_internal() ? at(0) : 0; }
    Entry k() const { return is_leaf() ? at(4) : -1; }
    bool is_leaf() const { return size() == 5; }
    bool is_internal() const { return size() < 5; }
    void back_to_zero() { at(0) = at(1) = at(2) = at(3) = 0; }
    friend std::ostream& operator<<(std::ostream& os, const FiveTuple& obj) {
        os << AUTOQ::Util::Convert::ToString(static_cast<stdvectorboostmultiprecisioncpp_int>(obj));
        return os;
    }
    FiveTuple operator+(const FiveTuple &o) const { return binary_operation(o, true); }
    FiveTuple operator-(const FiveTuple &o) const { return binary_operation(o, false); }
    FiveTuple binary_operation(const FiveTuple &o, bool add) const {
        assert(this->at(4) == o.at(4)); // Two k's must be the same.
        FiveTuple symbol;
        for (int i=0; i<4; i++) { // We do not change k here.
            if (add) symbol.push_back(this->at(i) + o.at(i));
            else symbol.push_back(this->at(i) - o.at(i));
            // if ((a>=0 && b>=0 && a>std::numeric_limits<Entry>::max()-b)
            //  || (a<0 && b<0 && a<std::numeric_limits<Entry>::min()-b))
            //     throw std::overflow_error("");
        }
        symbol.push_back(this->at(4)); // remember to push k
        return symbol;
    }
    FiveTuple operator*(const FiveTuple &o) const {
        FiveTuple symbol;
        symbol.push_back(at(0)*o.at(0) - at(1)*o.at(3) - at(2)*o.at(2) - at(3)*o.at(1));
        symbol.push_back(at(0)*o.at(1) + at(1)*o.at(0) - at(2)*o.at(3) - at(3)*o.at(2));
        symbol.push_back(at(0)*o.at(2) + at(1)*o.at(1) + at(2)*o.at(0) - at(3)*o.at(3));
        symbol.push_back(at(0)*o.at(3) + at(1)*o.at(2) + at(2)*o.at(1) + at(3)*o.at(0));
        symbol.push_back(at(4) + o.at(4)); // remember to push k
        return symbol;
    }
    void fraction_simplification() { // TODO: still don't know if it is required or not.
        if (at(0)==0 && at(1)==0 && at(2)==0 && at(3)==0) at(4) = 0;
        else {
            while ((at(0)&1)==0 && (at(1)&1)==0 && (at(2)&1)==0 && (at(3)&1)==0 && at(4)>=2) { // Notice the parentheses enclosing at(i)&1 are very important! HAHA
                for (int i=0; i<4; i++) at(i) /= 2;
                at(4) -= 2;
            }
        }
    }
    FiveTuple& divide_by_the_square_root_of_two(int times=1) {
        assert(times >= 0);
        at(4) += times;
        return *this;
    }
    void clockwise(int times=1) {
        assert(times >= 0);
        while (times--) {
            auto t = at(0);
            for (int i=0; i<3; i++) {
                at(i) = at(i+1);
            }
            at(3) = -t;
        }
    }
    void counterclockwise(int times=1) {
        assert(times >= 0);
        while (times--) {
            auto t = at(3);
            for (int i=2; i>=0; i--) {
                at(i+1) = at(i);
            }
            at(0) = -t;
        }
    }
    FiveTuple& negate() {
        for (int i=0; i<4; i++)
            at(i) = -at(i);
        return *this;
    }
};

#endif