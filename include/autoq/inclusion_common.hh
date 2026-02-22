#ifndef _AUTOQ_INCLUSION_COMMON_HH_
#define _AUTOQ_INCLUSION_COMMON_HH_

#include "autoq/autoq.hh"

#ifdef AUTOQ_INCLUSION_DEBUG
#define INCLUSION_DEBUG(msg) AUTOQ_DEBUG(msg)
#else
#define INCLUSION_DEBUG(msg) do {} while (0)
#endif

#endif
