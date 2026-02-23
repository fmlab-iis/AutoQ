/** Macros used by gate implementations. Include in .cc after aut_description.hh (State in scope). */
#ifndef AUTOQ_GATE_MACROS_HH
#define AUTOQ_GATE_MACROS_HH

// #define TO_QASM
#define QASM_FILENAME "circuit.qasm"

#define L(s1, s2) (stateNum + (s1) * stateNum + (s2))
#define R(s1, s2) (stateNum + stateNum * stateNum + (s1) * stateNum + (s2))

#define queryTopID(oldID, newID)    State newID = oldID + stateNum;
#define queryChildID(oldID, newID)  State newID = oldID + stateNum;

#define queryTopID2(oldID, newID)   State newID = oldID + stateNum * 2;
#define queryChildID2(oldID, newID) State newID = oldID + stateNum * 2;

#endif
