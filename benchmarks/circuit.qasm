OPENQASM 3.0;
include "stdgates.inc";
qubit[2] qb;

//x qubits[1];
h qubits[1];
cx qubits[0], qubits[1];