OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[25];

h qubits[24];
h qubits[23];
h qubits[22];
h qubits[21];
h qubits[20];
h qubits[19];
h qubits[18];
h qubits[17];
h qubits[16];
h qubits[15];
h qubits[14];
h qubits[13];
h qubits[12];
z qubits[24];
ccx qubits[0], qubits[12], qubits[24];
ccx qubits[1], qubits[13], qubits[24];
ccx qubits[2], qubits[14], qubits[24];
ccx qubits[3], qubits[15], qubits[24];
ccx qubits[4], qubits[16], qubits[24];
ccx qubits[5], qubits[17], qubits[24];
ccx qubits[6], qubits[18], qubits[24];
ccx qubits[7], qubits[19], qubits[24];
ccx qubits[8], qubits[20], qubits[24];
ccx qubits[9], qubits[21], qubits[24];
ccx qubits[10], qubits[22], qubits[24];
ccx qubits[11], qubits[23], qubits[24];
h qubits[24];
h qubits[23];
h qubits[22];
h qubits[21];
h qubits[20];
h qubits[19];
h qubits[18];
h qubits[17];
h qubits[16];
h qubits[15];
h qubits[14];
h qubits[13];
h qubits[12];