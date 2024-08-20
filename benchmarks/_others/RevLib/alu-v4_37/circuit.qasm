OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[5];

cx qubits[3], qubits[4];
cx qubits[2], qubits[1];
x qubits[2];
ccx qubits[3], qubits[1], qubits[2];
cx qubits[2], qubits[0];
ccx qubits[4], qubits[0], qubits[2];
cx qubits[2], qubits[4];
