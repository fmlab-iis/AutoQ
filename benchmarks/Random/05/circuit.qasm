OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[5];

z qubits[1];
rx(pi/2) qubits[2];
t qubits[1];
ry(pi/2) qubits[0];
s qubits[4];
h qubits[1];
cz qubits[1], qubits[4];
s qubits[2];
x qubits[0];
cz qubits[0], qubits[4];
ccx qubits[4], qubits[3], qubits[0];
ry(pi/2) qubits[3];
s qubits[3];
h qubits[4];
z qubits[1];
