OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[10];

ccx qubits[0], qubits[1], qubits[2];
ccx qubits[3], qubits[2], qubits[4];
ccx qubits[5], qubits[4], qubits[6];
ccx qubits[7], qubits[6], qubits[8];
cx qubits[8], qubits[9];
ccx qubits[7], qubits[6], qubits[8];
ccx qubits[5], qubits[4], qubits[6];
ccx qubits[3], qubits[2], qubits[4];
ccx qubits[0], qubits[1], qubits[2];
