OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[8];

cz qubits[4], qubits[3];
z qubits[5];
h qubits[6];
cx qubits[0], qubits[2];
y qubits[0];
ccx qubits[5], qubits[4], qubits[7];
ry(pi/2) qubits[7];
y qubits[3];
z qubits[5];
z qubits[6];
z qubits[3];
y qubits[2];
ry(pi/2) qubits[2];
ccx qubits[0], qubits[5], qubits[3];
rx(pi/2) qubits[4];
y qubits[3];
h qubits[4];
ccx qubits[7], qubits[2], qubits[0];
y qubits[6];
x qubits[2];
h qubits[1];
z qubits[2];
cx qubits[1], qubits[0];
cz qubits[4], qubits[2];