OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[5];

cx qubits[3], qubits[4];
x qubits[3];
cx qubits[1], qubits[2];
ccx qubits[3], qubits[2], qubits[1];
cx qubits[1], qubits[0];
x qubits[1];
ccx qubits[4], qubits[0], qubits[1];
