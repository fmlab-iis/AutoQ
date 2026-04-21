OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[12];

h qubits[0];
cx qubits[0], qubits[1];
cx qubits[1], qubits[2];
cx qubits[2], qubits[3];
cx qubits[3], qubits[4];
cx qubits[4], qubits[5];
cx qubits[5], qubits[6];
cx qubits[6], qubits[7];
cx qubits[7], qubits[8];
cx qubits[8], qubits[9];
cx qubits[9], qubits[10];
cx qubits[10], qubits[11];
