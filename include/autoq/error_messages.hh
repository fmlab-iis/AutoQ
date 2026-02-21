#ifndef _AUTOQ_ERROR_MESSAGES_HH_
#define _AUTOQ_ERROR_MESSAGES_HH_

namespace AUTOQ {
namespace ErrorMessages {

// File I/O
inline constexpr const char* kOpenFilePrefix = "Failed to open file ";

// Circuit / execution
inline constexpr const char* kUnsupportedGatePrefix = "unsupported gate: ";
inline constexpr const char* kQubitMismatch = "The number of qubits in the automaton does not match the number of qubits in the circuit.";
inline constexpr const char* kNestedLoops = "Nested loops are not supported yet.";
inline constexpr const char* kLoopNotEnded = "Loop not ended properly";
inline constexpr const char* kLoopInvariantPredicate = "The loop invariant cannot be a predicate automaton.";
inline constexpr const char* kLoopInvariantType = "The provided type of the loop invariant is not supported yet.";

// CLI / verification
inline constexpr const char* kPredicatePrecondition = "Predicate amplitudes cannot be used in a precondition.";
inline constexpr const char* kPredicateAutomataPost = "PredicateAutomata as the postcondition are currently not supported.";
inline constexpr const char* kConcretePostPre = "When the postcondition has only concrete amplitudes, the precondition must also do so.";
inline constexpr const char* kUnsupportedPostType = "Unsupported type of the postcondition.";
inline constexpr const char* kNoMode = "Please provide at least one mode. Run \"autoq -h\" for more information.";

}  // namespace ErrorMessages
}  // namespace AUTOQ

#endif
