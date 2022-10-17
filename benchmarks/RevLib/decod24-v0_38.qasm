OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[4];

ccx qubits[3], qubits[2], qubits[0];
cx qubits[2], qubits[3];
ccx qubits[3], qubits[2], qubits[1];
ccx qubits[2], qubits[0], qubits[3];
cx qubits[3], qubits[2];
x qubits[3];
