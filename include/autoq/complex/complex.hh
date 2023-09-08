#ifndef _AUTOQ_COMPLEX_HH_
#define _AUTOQ_COMPLEX_HH_

#include <autoq/complex/plain.hh>
#include <autoq/complex/fivetuple.hh>

namespace AUTOQ
{
    namespace Complex
    {
        struct FiveTuple;
        struct Plain;
        #if COMPLEX == 1
            using Complex = FiveTuple;
        #else
            using Complex = Plain;
        #endif
    }
}

#endif