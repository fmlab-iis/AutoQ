OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[4];

h qubits[3];
x qubits[3];
h qubits[3];
h qubits[2];
x qubits[2];
h qubits[2];
h qubits[1];
x qubits[1];
h qubits[1];
h qubits[0];
x qubits[0];
h qubits[0];
