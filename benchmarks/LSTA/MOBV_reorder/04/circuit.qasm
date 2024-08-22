OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[9];

h qubits[8];
h qubits[7];
h qubits[5];
h qubits[3];
h qubits[1];
z qubits[8];
ccx qubits[0], qubits[1], qubits[8];
ccx qubits[2], qubits[3], qubits[8];
ccx qubits[4], qubits[5], qubits[8];
ccx qubits[6], qubits[7], qubits[8];
h qubits[8];
h qubits[7];
h qubits[5];
h qubits[3];
h qubits[1];
