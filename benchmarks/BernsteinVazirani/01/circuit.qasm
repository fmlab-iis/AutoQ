OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[2];

h qubits[0];
h qubits[1];
z qubits[1];
cx qubits[0], qubits[1];
h qubits[0];
h qubits[1];
