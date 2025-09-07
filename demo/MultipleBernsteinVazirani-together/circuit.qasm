OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[7];

h qubits[6];
h qubits[5];
h qubits[4];
h qubits[3];
z qubits[6];
ccx qubits[0], qubits[3], qubits[6];
ccx qubits[1], qubits[4], qubits[6];
ccx qubits[2], qubits[5], qubits[6];
h qubits[6];
h qubits[5];
h qubits[4];
h qubits[3];
