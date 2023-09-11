#ifndef _AUTOQ_COMPLEX_HH_
#define _AUTOQ_COMPLEX_HH_

#include <autoq/complex/plain.hh>
#include <autoq/complex/fivetuple.hh>

template <typename T>
concept is_complex = requires (const T &x, T y, int z, boost::rational<boost::multiprecision::cpp_int> theta) {
    new T(theta);
    new T(z);
    { T::Angle(theta) } -> std::same_as<T>;
    { T::One() } -> std::same_as<T>;
    { T::Zero() } -> std::same_as<T>;
    { T::Rand() } -> std::same_as<T>;
    { T::sqrt2() } -> std::same_as<T>;
    { std::cout << x } -> std::same_as<decltype(std::cout)&>; // https://tjsw.medium.com/潮-c-20-concepts-c-編譯期檢查的正派道路-3db8bec914a4
    { x + x } -> std::same_as<T>;
    { x - x } -> std::same_as<T>;
    { x * x } -> std::same_as<T>;
    { x / x } -> std::same_as<T>;
    { y.fraction_simplification() } -> std::same_as<T&>;
    { y.divide_by_the_square_root_of_two(z) } -> std::same_as<T&>;
    { y.counterclockwise(theta) } -> std::same_as<T&>;
    { y.clockwise(theta) } -> std::same_as<T&>;
    { x.toInt() } -> std::same_as<boost::multiprecision::cpp_int>;
    { x.to_rational() } -> std::same_as<boost::rational<boost::multiprecision::cpp_int>>;
    { x.realToSMT() } -> std::same_as<std::string>;
    { x.imagToSMT() } -> std::same_as<std::string>;
    { x.abs2() } -> std::same_as<double>;
    { x == x } -> std::same_as<bool>;
    { x < x } -> std::same_as<bool>;
    { x.isZero() } -> std::same_as<bool>;
};

namespace AUTOQ
{
    namespace Complex
    {
        /* Users can define multiple types of amplitudes in the following line, */
        struct FiveTuple;
        struct Plain;
        #if COMPLEX == 1
            using Complex = FiveTuple;
        #else
            using Complex = Plain;
        #endif
        // but we can use only one type at a same time.
        static_assert(is_complex<Complex>, "The used type must implement all required member functions!");
    }
}

#endif