OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[6];

cx qubits[3], qubits[0];
cx qubits[1], qubits[0];
cx qubits[5], qubits[0];
x qubits[2];
cx qubits[2], qubits[0];
x qubits[4];
cx qubits[4], qubits[0];
