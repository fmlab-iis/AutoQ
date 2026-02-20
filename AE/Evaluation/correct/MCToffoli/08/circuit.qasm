OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[16];

ccx qubits[0], qubits[1], qubits[8];
ccx qubits[8], qubits[2], qubits[9];
ccx qubits[9], qubits[3], qubits[10];
ccx qubits[10], qubits[4], qubits[11];
ccx qubits[11], qubits[5], qubits[12];
ccx qubits[12], qubits[6], qubits[13];
ccx qubits[13], qubits[7], qubits[14];
cx qubits[14], qubits[15];
ccx qubits[13], qubits[7], qubits[14];
ccx qubits[12], qubits[6], qubits[13];
ccx qubits[11], qubits[5], qubits[12];
ccx qubits[10], qubits[4], qubits[11];
ccx qubits[9], qubits[3], qubits[10];
ccx qubits[8], qubits[2], qubits[9];
ccx qubits[0], qubits[1], qubits[8];
