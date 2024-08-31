OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[5];

h qubits[4];
h qubits[3];
h qubits[1];
z qubits[4];
ccx qubits[0], qubits[1], qubits[4];
ccx qubits[2], qubits[3], qubits[4];
h qubits[4];
h qubits[3];
h qubits[1];
