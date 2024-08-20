OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[4];

h qubits[0];
h qubits[1];
h qubits[2];
h qubits[3];
z qubits[3];
cx qubits[0], qubits[3];
cx qubits[2], qubits[3];
h qubits[0];
h qubits[1];
h qubits[2];
h qubits[3];
