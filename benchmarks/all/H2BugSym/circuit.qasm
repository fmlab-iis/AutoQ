OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[1];

h qubits[0];
y qubits[0]; // x takes 57 seconds.