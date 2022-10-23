OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[6];

ccx qubits[0], qubits[1], qubits[2];
ccx qubits[3], qubits[2], qubits[4];
cx qubits[4], qubits[5];
ccx qubits[3], qubits[2], qubits[4];
ccx qubits[0], qubits[1], qubits[2];
