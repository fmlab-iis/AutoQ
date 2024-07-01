OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[8];

h qubits[0];
cx qubits[0], qubits[1];
cx qubits[1], qubits[2];
cx qubits[2], qubits[3];
cx qubits[3], qubits[4];
cx qubits[4], qubits[5];
cx qubits[5], qubits[6];
