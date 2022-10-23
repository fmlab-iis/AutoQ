OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[4];

x qubits[2];
rx(pi/2) qubits[2];
ccx qubits[3], qubits[1], qubits[2];
ccx qubits[2], qubits[1], qubits[3];
ry(pi/2) qubits[0];
z qubits[2];
ry(pi/2) qubits[1];
s qubits[3];
x qubits[1];
s qubits[0];
ry(pi/2) qubits[2];
cx qubits[2], qubits[3];
