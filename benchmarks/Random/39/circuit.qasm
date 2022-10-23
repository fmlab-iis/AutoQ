OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[39];

y qubits[25];
x qubits[37];
z qubits[32];
ry(pi/2) qubits[24];
y qubits[38];
s qubits[1];
cz qubits[19], qubits[24];
y qubits[27];
x qubits[21];
cx qubits[14], qubits[17];
s qubits[1];
s qubits[14];
s qubits[31];
s qubits[28];
cx qubits[37], qubits[3];
rx(pi/2) qubits[24];
s qubits[25];
x qubits[6];
x qubits[17];
t qubits[15];
t qubits[26];
s qubits[6];
z qubits[16];
rx(pi/2) qubits[20];
cx qubits[6], qubits[13];
rx(pi/2) qubits[16];
rx(pi/2) qubits[13];
h qubits[2];
h qubits[1];
s qubits[33];
rx(pi/2) qubits[13];
y qubits[19];
cx qubits[10], qubits[22];
ry(pi/2) qubits[28];
cz qubits[7], qubits[15];
h qubits[13];
h qubits[32];
z qubits[1];
ccx qubits[25], qubits[3], qubits[11];
cx qubits[20], qubits[14];
x qubits[11];
rx(pi/2) qubits[29];
cz qubits[0], qubits[23];
rx(pi/2) qubits[4];
cz qubits[33], qubits[14];
h qubits[4];
x qubits[30];
ccx qubits[7], qubits[3], qubits[27];
t qubits[33];
x qubits[29];
ccx qubits[20], qubits[2], qubits[11];
t qubits[5];
s qubits[1];
z qubits[30];
cx qubits[27], qubits[14];
y qubits[31];
s qubits[15];
cz qubits[38], qubits[19];
ry(pi/2) qubits[29];
ccx qubits[34], qubits[36], qubits[13];
rx(pi/2) qubits[25];
y qubits[28];
y qubits[16];
z qubits[7];
t qubits[28];
t qubits[27];
ry(pi/2) qubits[11];
y qubits[20];
cz qubits[22], qubits[12];
h qubits[18];
ry(pi/2) qubits[27];
h qubits[36];
cz qubits[36], qubits[6];
h qubits[33];
ccx qubits[31], qubits[9], qubits[16];
cz qubits[25], qubits[21];
y qubits[32];
h qubits[25];
y qubits[25];
h qubits[33];
ccx qubits[24], qubits[22], qubits[5];
ry(pi/2) qubits[4];
z qubits[3];
cx qubits[18], qubits[28];
rx(pi/2) qubits[15];
s qubits[16];
rx(pi/2) qubits[4];
z qubits[8];
z qubits[7];
ry(pi/2) qubits[30];
x qubits[4];
y qubits[29];
s qubits[4];
cx qubits[31], qubits[37];
x qubits[4];
z qubits[34];
cx qubits[4], qubits[37];
t qubits[22];
t qubits[12];
cz qubits[12], qubits[17];
z qubits[5];
ry(pi/2) qubits[12];
cz qubits[11], qubits[34];
ry(pi/2) qubits[4];
rx(pi/2) qubits[13];
cz qubits[25], qubits[17];
s qubits[6];
s qubits[13];
ry(pi/2) qubits[35];
x qubits[7];
rx(pi/2) qubits[35];
ry(pi/2) qubits[11];
ccx qubits[26], qubits[38], qubits[13];
ccx qubits[14], qubits[7], qubits[8];
t qubits[11];
ccx qubits[10], qubits[35], qubits[23];
y qubits[37];