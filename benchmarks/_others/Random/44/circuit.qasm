OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[44];

h qubits[19];
cx qubits[22], qubits[3];
ccx qubits[42], qubits[25], qubits[12];
x qubits[35];
y qubits[36];
ccx qubits[41], qubits[11], qubits[4];
h qubits[25];
s qubits[13];
cz qubits[28], qubits[2];
cz qubits[7], qubits[42];
y qubits[12];
s qubits[29];
s qubits[34];
s qubits[2];
h qubits[24];
x qubits[15];
y qubits[32];
rx(pi/2) qubits[0];
z qubits[38];
cz qubits[11], qubits[18];
ccx qubits[12], qubits[23], qubits[43];
ccx qubits[27], qubits[21], qubits[40];
y qubits[20];
rx(pi/2) qubits[22];
z qubits[13];
h qubits[1];
s qubits[5];
s qubits[4];
rx(pi/2) qubits[30];
s qubits[38];
y qubits[37];
t qubits[7];
z qubits[5];
y qubits[21];
rx(pi/2) qubits[0];
cz qubits[37], qubits[28];
cz qubits[9], qubits[38];
ry(pi/2) qubits[37];
s qubits[29];
s qubits[40];
cx qubits[6], qubits[1];
x qubits[11];
t qubits[28];
s qubits[41];
cx qubits[17], qubits[35];
z qubits[9];
t qubits[25];
rx(pi/2) qubits[10];
s qubits[27];
y qubits[30];
h qubits[32];
x qubits[19];
y qubits[37];
z qubits[27];
x qubits[10];
cz qubits[11], qubits[8];
cz qubits[38], qubits[37];
x qubits[12];
y qubits[18];
h qubits[14];
h qubits[40];
s qubits[9];
s qubits[41];
y qubits[5];
h qubits[13];
z qubits[4];
cx qubits[34], qubits[41];
ccx qubits[17], qubits[7], qubits[19];
s qubits[18];
t qubits[23];
ccx qubits[40], qubits[43], qubits[0];
cx qubits[37], qubits[24];
cz qubits[16], qubits[20];
h qubits[2];
x qubits[9];
h qubits[3];
z qubits[4];
t qubits[37];
y qubits[26];
y qubits[1];
ccx qubits[17], qubits[20], qubits[1];
x qubits[23];
x qubits[0];
cz qubits[0], qubits[26];
z qubits[0];
h qubits[30];
ry(pi/2) qubits[15];
ccx qubits[18], qubits[0], qubits[22];
ccx qubits[33], qubits[26], qubits[13];
s qubits[39];
rx(pi/2) qubits[37];
ry(pi/2) qubits[14];
ccx qubits[36], qubits[22], qubits[35];
h qubits[42];
x qubits[12];
ry(pi/2) qubits[14];
s qubits[19];
rx(pi/2) qubits[32];
s qubits[8];
cz qubits[10], qubits[8];
cz qubits[31], qubits[42];
y qubits[21];
z qubits[40];
t qubits[37];
y qubits[7];
s qubits[24];
ccx qubits[2], qubits[15], qubits[11];
x qubits[3];
z qubits[18];
s qubits[26];
s qubits[10];
h qubits[29];
t qubits[10];
rx(pi/2) qubits[22];
rx(pi/2) qubits[2];
ry(pi/2) qubits[29];
y qubits[41];
y qubits[16];
y qubits[33];
y qubits[38];
z qubits[42];
ry(pi/2) qubits[5];
cz qubits[16], qubits[28];
cz qubits[35], qubits[21];
x qubits[28];
ry(pi/2) qubits[1];
z qubits[21];
x qubits[28];
ccx qubits[16], qubits[31], qubits[40];
y qubits[10];
z qubits[23];
z qubits[3];