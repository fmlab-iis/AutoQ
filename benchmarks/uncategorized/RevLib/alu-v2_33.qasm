OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[5];

x qubits[4];
cx qubits[3], qubits[4];
cx qubits[2], qubits[1];
ccx qubits[3], qubits[1], qubits[2];
cx qubits[0], qubits[2];
x qubits[0];
ccx qubits[4], qubits[2], qubits[0];
