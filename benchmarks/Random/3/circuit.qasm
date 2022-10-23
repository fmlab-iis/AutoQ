OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[3];

rx(pi/2) qubits[1];
rx(pi/2) qubits[1];
y qubits[1];
x qubits[0];
h qubits[1];
cx qubits[1], qubits[2];
h qubits[2];
s qubits[0];
ccx qubits[1], qubits[2], qubits[0];
