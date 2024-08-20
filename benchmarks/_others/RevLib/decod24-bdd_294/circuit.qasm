OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[6];

ccx qubits[0], qubits[1], qubits[2];
ccx qubits[0], qubits[1], qubits[3];
cx qubits[0], qubits[3];
ccx qubits[0], qubits[1], qubits[4];
cx qubits[1], qubits[4];
cx qubits[0], qubits[5];
ccx qubits[0], qubits[1], qubits[5];
cx qubits[1], qubits[5];
x qubits[3];
x qubits[4];
x qubits[5];
