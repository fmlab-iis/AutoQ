OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[5];

h qubits[0];
cx qubits[0], qubits[1];
cx qubits[1], qubits[2];
cx qubits[2], qubits[3];
cx qubits[3], qubits[4];
