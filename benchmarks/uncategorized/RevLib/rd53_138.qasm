OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[8];

ccx qubits[0], qubits[1], qubits[5];
cx qubits[0], qubits[1];
ccx qubits[2], qubits[5], qubits[6];
ccx qubits[1], qubits[2], qubits[5];
cx qubits[1], qubits[2];
ccx qubits[3], qubits[6], qubits[7];
ccx qubits[3], qubits[5], qubits[6];
ccx qubits[2], qubits[3], qubits[5];
cx qubits[2], qubits[3];
ccx qubits[4], qubits[6], qubits[7];
ccx qubits[3], qubits[4], qubits[5];
cx qubits[3], qubits[4];
