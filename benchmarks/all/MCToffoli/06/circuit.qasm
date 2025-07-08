OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[12];

ccx qubits[0], qubits[1], qubits[6];
ccx qubits[6], qubits[2], qubits[7];
ccx qubits[7], qubits[3], qubits[8];
ccx qubits[8], qubits[4], qubits[9];
ccx qubits[9], qubits[5], qubits[10];
cx qubits[10], qubits[11];
ccx qubits[9], qubits[5], qubits[10];
ccx qubits[8], qubits[4], qubits[9];
ccx qubits[7], qubits[3], qubits[8];
ccx qubits[6], qubits[2], qubits[7];
ccx qubits[0], qubits[1], qubits[6];
