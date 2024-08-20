OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[5];

cx qubits[4], qubits[0];
x qubits[4];
ccx qubits[2], qubits[1], qubits[0];
cx qubits[0], qubits[4];
