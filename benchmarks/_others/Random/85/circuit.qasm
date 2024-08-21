OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[85];

y qubits[28];
y qubits[47];
s qubits[51];
cz qubits[6], qubits[66];
rx(pi/2) qubits[1];
y qubits[58];
t qubits[3];
cz qubits[41], qubits[71];
ccx qubits[7], qubits[10], qubits[50];
z qubits[72];
x qubits[46];
y qubits[35];
t qubits[19];
ccx qubits[1], qubits[48], qubits[42];
rx(pi/2) qubits[13];
z qubits[35];
cx qubits[31], qubits[82];
x qubits[2];
z qubits[19];
ccx qubits[39], qubits[60], qubits[34];
cx qubits[68], qubits[2];
y qubits[63];
ry(pi/2) qubits[21];
h qubits[36];
h qubits[63];
z qubits[1];
z qubits[60];
y qubits[27];
ry(pi/2) qubits[51];
ry(pi/2) qubits[49];
rx(pi/2) qubits[16];
z qubits[84];
t qubits[45];
ry(pi/2) qubits[25];
ccx qubits[38], qubits[65], qubits[46];
cz qubits[28], qubits[24];
t qubits[49];
t qubits[22];
y qubits[69];
y qubits[20];
x qubits[52];
h qubits[76];
t qubits[71];
y qubits[4];
cz qubits[27], qubits[73];
rx(pi/2) qubits[55];
x qubits[70];
y qubits[11];
x qubits[18];
cz qubits[64], qubits[46];
x qubits[51];
cx qubits[2], qubits[30];
cz qubits[28], qubits[22];
x qubits[77];
cx qubits[27], qubits[68];
x qubits[13];
s qubits[76];
rx(pi/2) qubits[19];
z qubits[19];
t qubits[55];
x qubits[71];
x qubits[70];
t qubits[38];
rx(pi/2) qubits[8];
rx(pi/2) qubits[58];
cz qubits[78], qubits[45];
rx(pi/2) qubits[21];
rx(pi/2) qubits[52];
rx(pi/2) qubits[15];
ry(pi/2) qubits[80];
y qubits[49];
h qubits[78];
rx(pi/2) qubits[50];
ry(pi/2) qubits[20];
s qubits[70];
t qubits[68];
cx qubits[52], qubits[30];
h qubits[59];
z qubits[37];
s qubits[54];
t qubits[35];
s qubits[9];
s qubits[67];
ry(pi/2) qubits[75];
z qubits[60];
s qubits[24];
ry(pi/2) qubits[70];
cz qubits[55], qubits[0];
z qubits[11];
cx qubits[70], qubits[36];
rx(pi/2) qubits[38];
h qubits[81];
ry(pi/2) qubits[18];
s qubits[44];
s qubits[21];
ccx qubits[45], qubits[72], qubits[11];
s qubits[9];
rx(pi/2) qubits[3];
ry(pi/2) qubits[77];
ry(pi/2) qubits[74];
h qubits[11];
ry(pi/2) qubits[20];
t qubits[12];
h qubits[0];
rx(pi/2) qubits[40];
x qubits[29];
z qubits[49];
s qubits[70];
cx qubits[78], qubits[48];
ry(pi/2) qubits[38];
x qubits[12];
h qubits[2];
y qubits[27];
cx qubits[4], qubits[12];
x qubits[66];
t qubits[18];
s qubits[37];
ry(pi/2) qubits[47];
ccx qubits[79], qubits[3], qubits[74];
x qubits[39];
ry(pi/2) qubits[28];
cx qubits[4], qubits[21];
ccx qubits[6], qubits[17], qubits[65];
h qubits[40];
cz qubits[73], qubits[24];
rx(pi/2) qubits[34];
cx qubits[69], qubits[15];
x qubits[45];
t qubits[54];
s qubits[21];
cx qubits[69], qubits[66];
cx qubits[7], qubits[20];
z qubits[78];
ccx qubits[37], qubits[56], qubits[31];
ccx qubits[73], qubits[54], qubits[19];
ry(pi/2) qubits[36];
rx(pi/2) qubits[10];
ccx qubits[83], qubits[4], qubits[73];
cz qubits[20], qubits[33];
y qubits[31];
x qubits[50];
t qubits[7];
ccx qubits[74], qubits[57], qubits[8];
x qubits[50];
x qubits[59];
ccx qubits[41], qubits[18], qubits[52];
x qubits[79];
s qubits[3];
cz qubits[5], qubits[7];
h qubits[51];
z qubits[54];
ccx qubits[71], qubits[84], qubits[60];
ccx qubits[6], qubits[54], qubits[17];
x qubits[0];
ccx qubits[3], qubits[22], qubits[81];
x qubits[82];
cz qubits[11], qubits[15];
rx(pi/2) qubits[63];
x qubits[22];
ry(pi/2) qubits[51];
ccx qubits[31], qubits[49], qubits[36];
cx qubits[19], qubits[65];
rx(pi/2) qubits[60];
ccx qubits[65], qubits[66], qubits[52];
cz qubits[18], qubits[9];
rx(pi/2) qubits[64];
t qubits[26];
t qubits[29];
h qubits[2];
ccx qubits[70], qubits[65], qubits[52];
z qubits[45];
s qubits[33];
rx(pi/2) qubits[24];
y qubits[60];
x qubits[6];
cx qubits[60], qubits[4];
z qubits[84];
y qubits[8];
x qubits[22];
t qubits[38];
t qubits[64];
y qubits[40];
x qubits[74];
z qubits[49];
y qubits[7];
ry(pi/2) qubits[57];
h qubits[46];
s qubits[7];
cx qubits[23], qubits[49];
z qubits[11];
s qubits[40];
h qubits[66];
cx qubits[30], qubits[40];
cz qubits[25], qubits[79];
y qubits[46];
s qubits[42];
z qubits[55];
ry(pi/2) qubits[32];
h qubits[48];
y qubits[80];
cx qubits[48], qubits[1];
z qubits[78];
ccx qubits[1], qubits[30], qubits[34];
ccx qubits[27], qubits[55], qubits[49];
y qubits[42];
z qubits[28];
cx qubits[82], qubits[72];
ccx qubits[63], qubits[71], qubits[53];
ccx qubits[27], qubits[42], qubits[14];
h qubits[44];
z qubits[19];
z qubits[10];
h qubits[0];
t qubits[14];
x qubits[25];
cx qubits[15], qubits[37];
z qubits[53];
ccx qubits[6], qubits[81], qubits[62];
cx qubits[25], qubits[48];
h qubits[12];
z qubits[57];
t qubits[16];
z qubits[70];
ccx qubits[80], qubits[4], qubits[67];
ccx qubits[17], qubits[68], qubits[81];
h qubits[55];
ry(pi/2) qubits[70];
rx(pi/2) qubits[58];
x qubits[80];
x qubits[37];
t qubits[72];
cz qubits[59], qubits[77];
y qubits[28];
x qubits[36];
y qubits[67];
h qubits[51];
s qubits[60];
x qubits[24];
ry(pi/2) qubits[30];
ccx qubits[19], qubits[60], qubits[61];
s qubits[46];
rx(pi/2) qubits[12];
cx qubits[84], qubits[22];
cz qubits[75], qubits[10];
t qubits[6];
rx(pi/2) qubits[4];
s qubits[10];
ry(pi/2) qubits[15];
cz qubits[62], qubits[23];
h qubits[37];
ccx qubits[57], qubits[17], qubits[22];
rx(pi/2) qubits[78];
s qubits[82];
s qubits[1];
x qubits[2];