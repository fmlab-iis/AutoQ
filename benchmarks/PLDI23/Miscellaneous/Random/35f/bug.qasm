OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[35];

y qubits[27];
y qubits[32];
rx(pi/2) qubits[29];
s qubits[3];
rx(pi/2) qubits[33];
cx qubits[32], qubits[15];
s qubits[34];
ccx qubits[19], qubits[14], qubits[3];
cx qubits[3], qubits[15];
x qubits[3];
h qubits[24];
ccx qubits[14], qubits[4], qubits[24];
t qubits[25];
x qubits[25];
ry(pi/2) qubits[2];
z qubits[26];
x qubits[27];
cz qubits[18], qubits[25];
ccx qubits[7], qubits[1], qubits[27];
z qubits[27];
z qubits[32];
z qubits[0];
ccx qubits[11], qubits[23], qubits[3];
cx qubits[2], qubits[19];
x qubits[21];
cz qubits[32], qubits[23];
rx(pi/2) qubits[34];
y qubits[12];
s qubits[1];
h qubits[0];
ccx qubits[29], qubits[19], qubits[5];
cx qubits[22], qubits[9];
ccx qubits[31], qubits[5], qubits[19];
ry(pi/2) qubits[28];
t qubits[26];
z qubits[21];
cz qubits[11], qubits[19];
cx qubits[8], qubits[20];
y qubits[19];
ccx qubits[30], qubits[1], qubits[18];
ry(pi/2) qubits[13];
s qubits[2];
cx qubits[4], qubits[13];
rx(pi/2) qubits[13];
ccx qubits[4], qubits[31], qubits[17];
rx(pi/2) qubits[24];
h qubits[17];
ccx qubits[0], qubits[5], qubits[9];
rx(pi/2) qubits[14];
h qubits[16];
ccx qubits[26], qubits[33], qubits[16];
ccx qubits[29], qubits[24], qubits[17];
cx qubits[3], qubits[26];
cx qubits[17], qubits[22];
h qubits[14];
cz qubits[6], qubits[8];
s qubits[8];
cx qubits[12], qubits[5];
s qubits[29];
x qubits[6];
ccx qubits[33], qubits[23], qubits[29];
x qubits[33];
y qubits[28];
t qubits[11];
s qubits[32];
z qubits[1];
cx qubits[8], qubits[0];
y qubits[0];
cx qubits[23], qubits[8];
y qubits[31];
x qubits[9];
s qubits[17];
ry(pi/2) qubits[17];
x qubits[0];
s qubits[24];
s qubits[16];
cx qubits[16], qubits[9];
y qubits[27];
y qubits[24];
z qubits[32];
ccx qubits[27], qubits[32], qubits[1];
cx qubits[0], qubits[1];
y qubits[33];
rx(pi/2) qubits[20];
x qubits[12];
s qubits[0];
y qubits[4];
h qubits[22];
x qubits[7];
rx(pi/2) qubits[27];
ry(pi/2) qubits[25];
ry(pi/2) qubits[28];
t qubits[21];
x qubits[31];
s qubits[16];
rx(pi/2) qubits[30];
t qubits[18];
x qubits[23];
z qubits[29];
t qubits[12];
h qubits[23];
cx qubits[25], qubits[4];
ccx qubits[24], qubits[32], qubits[9];
cz qubits[2], qubits[9];
z qubits[33];
h qubits[33];