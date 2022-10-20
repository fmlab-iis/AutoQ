OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[7];

cx qubits[0], qubits[5];
ccx qubits[1], qubits[3], qubits[5];
ccx qubits[0], qubits[3], qubits[5];
cx qubits[2], qubits[6];
ccx qubits[0], qubits[3], qubits[6];
ccx qubits[2], qubits[3], qubits[6];
cx qubits[6], qubits[5];
ccx qubits[4], qubits[5], qubits[6];
x qubits[6];
