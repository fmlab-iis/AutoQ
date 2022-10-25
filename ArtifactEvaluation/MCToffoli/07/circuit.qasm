OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[14];

ccx qubits[0], qubits[1], qubits[2];
ccx qubits[3], qubits[2], qubits[4];
ccx qubits[5], qubits[4], qubits[6];
ccx qubits[7], qubits[6], qubits[8];
ccx qubits[9], qubits[8], qubits[10];
ccx qubits[11], qubits[10], qubits[12];
cx qubits[12], qubits[13];
ccx qubits[11], qubits[10], qubits[12];
ccx qubits[9], qubits[8], qubits[10];
ccx qubits[7], qubits[6], qubits[8];
ccx qubits[5], qubits[4], qubits[6];
ccx qubits[3], qubits[2], qubits[4];
ccx qubits[0], qubits[1], qubits[2];
