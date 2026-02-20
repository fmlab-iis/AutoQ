#ifndef _AUTOQ_PARSING_ANGLE_HH_
#define _AUTOQ_PARSING_ANGLE_HH_

#include "autoq/error.hh"
#include "autoq/parsing/ExtendedDirac/EvaluationVisitor.h"
#include <string>

namespace AUTOQ {
namespace Parsing {

/** Parse an angle string (e.g. "pi/2") to a rational. Replaces "pi" with
 *  pi_substitute before parsing. Throws if angle is not "0" and contains no "pi".
 *  pi_substitute is typically "(1/2)" for half-turns or "1" for a different scale. */
inline auto parse_angle_to_rational(std::string angle, const char* gate_name,
                                    const char* pi_substitute) {
    size_t pos = angle.find("pi");
    if (pos != std::string::npos) {
        angle.replace(pos, 2, pi_substitute);
    } else if (angle != "0") {
        THROW_AUTOQ_ERROR("The angle in " + std::string(gate_name) + " gate is not a multiple of pi!");
    }
    return EvaluationVisitor<>::ComplexParser(angle).getComplex().to_rational();
}

}  // namespace Parsing
}  // namespace AUTOQ

#endif
