OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[15];

h qubits[14];
h qubits[13];
h qubits[12];
h qubits[11];
h qubits[10];
h qubits[9];
h qubits[8];
h qubits[7];
z qubits[14];
ccx qubits[0], qubits[7], qubits[14];
ccx qubits[1], qubits[8], qubits[14];
ccx qubits[2], qubits[9], qubits[14];
ccx qubits[3], qubits[10], qubits[14];
ccx qubits[4], qubits[11], qubits[14];
ccx qubits[5], qubits[12], qubits[14];
ccx qubits[6], qubits[13], qubits[14];
h qubits[14];
h qubits[13];
h qubits[12];
h qubits[11];
h qubits[10];
h qubits[9];
h qubits[8];
h qubits[7];