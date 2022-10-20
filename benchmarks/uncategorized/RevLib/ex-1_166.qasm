OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[3];

cx qubits[0], qubits[1];
ccx qubits[1], qubits[2], qubits[0];
cx qubits[0], qubits[1];
x qubits[0];
