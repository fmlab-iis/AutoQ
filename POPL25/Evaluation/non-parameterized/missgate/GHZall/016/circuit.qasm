OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[16];

h qubits[0];
cx qubits[0], qubits[1];
cx qubits[1], qubits[2];
cx qubits[2], qubits[3];
cx qubits[3], qubits[4];
cx qubits[4], qubits[5];
cx qubits[5], qubits[6];
cx qubits[6], qubits[7];
cx qubits[8], qubits[9];
cx qubits[9], qubits[10];
cx qubits[10], qubits[11];
cx qubits[11], qubits[12];
cx qubits[12], qubits[13];
cx qubits[13], qubits[14];
cx qubits[14], qubits[15];
