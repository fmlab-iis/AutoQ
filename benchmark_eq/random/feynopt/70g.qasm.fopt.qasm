OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[70];
ccx qubits[48],qubits[55],qubits[45];
x qubits[19];
cz qubits[45],qubits[14];
t qubits[51];
ry(pi/2) qubits[27];
s qubits[65];
ry(pi/2) qubits[43];
z qubits[42];
rx(pi/2) qubits[25];
ry(pi/2) qubits[58];
cx qubits[53],qubits[68];
t qubits[37];
s qubits[30];
y qubits[59];
z qubits[65];
h qubits[46];
h qubits[17];
rx(pi/2) qubits[41];
t qubits[15];
z qubits[8];
t qubits[13];
ry(pi/2) qubits[43];
s qubits[9];
cx qubits[25],qubits[64];
s qubits[16];
ccx qubits[42],qubits[8],qubits[26];
x qubits[50];
cx qubits[6],qubits[12];
ccx qubits[53],qubits[59],qubits[12];
cz qubits[30],qubits[63];
cz qubits[60],qubits[14];
h qubits[4];
s qubits[24];
y qubits[3];
z qubits[28];
ccx qubits[30],qubits[57],qubits[56];
x qubits[7];
t qubits[7];
ccx qubits[49],qubits[13],qubits[11];
x qubits[8];
z qubits[12];
ccx qubits[35],qubits[54],qubits[26];
cx qubits[45],qubits[52];
x qubits[61];
rx(pi/2) qubits[8];
x qubits[48];
h qubits[35];
y qubits[36];
cz qubits[43],qubits[39];
rx(pi/2) qubits[68];
ry(pi/2) qubits[52];
z qubits[13];
s qubits[24];
h qubits[30];
x qubits[53];
h qubits[32];
t qubits[69];
h qubits[3];
ccx qubits[10],qubits[61],qubits[62];
y qubits[51];
rx(pi/2) qubits[52];
ry(pi/2) qubits[35];
x qubits[24];
cx qubits[69],qubits[34];
s qubits[63];
h qubits[17];
x qubits[59];
z qubits[40];
y qubits[34];
ry(pi/2) qubits[0];
cx qubits[47],qubits[31];
t qubits[31];
t qubits[4];
ry(pi/2) qubits[1];
x qubits[47];
cx qubits[36],qubits[12];
rx(pi/2) qubits[3];
x qubits[22];
ry(pi/2) qubits[45];
rx(pi/2) qubits[3];
s qubits[49];
ccx qubits[43],qubits[20],qubits[30];
ry(pi/2) qubits[10];
x qubits[5];
x qubits[3];
cx qubits[31],qubits[57];
h qubits[9];
s qubits[19];
ccx qubits[53],qubits[56],qubits[68];
h qubits[59];
ccx qubits[40],qubits[38],qubits[15];
rx(pi/2) qubits[41];
s qubits[47];
t qubits[63];
cx qubits[6],qubits[25];
y qubits[48];
ccx qubits[18],qubits[51],qubits[60];
s qubits[51];
rx(pi/2) qubits[58];
t qubits[43];
z qubits[35];
y qubits[55];
rx(pi/2) qubits[30];
ccx qubits[24],qubits[11],qubits[63];
z qubits[52];
h qubits[10];
rx(pi/2) qubits[19];
rx(pi/2) qubits[34];
rx(pi/2) qubits[50];
cx qubits[16],qubits[69];
z qubits[18];
cz qubits[69],qubits[42];
x qubits[50];
rx(pi/2) qubits[47];
z qubits[69];
z qubits[23];
cz qubits[11],qubits[47];
ry(pi/2) qubits[4];
h qubits[47];
y qubits[21];
s qubits[49];
ccx qubits[52],qubits[35],qubits[45];
cx qubits[63],qubits[56];
ccx qubits[11],qubits[58],qubits[23];
y qubits[49];
z qubits[22];
ry(pi/2) qubits[55];
s qubits[1];
cz qubits[5],qubits[12];
ccx qubits[57],qubits[29],qubits[8];
rx(pi/2) qubits[59];
t qubits[52];
rx(pi/2) qubits[35];
cz qubits[15],qubits[10];
s qubits[20];
s qubits[7];
cx qubits[67],qubits[42];
ry(pi/2) qubits[58];
rx(pi/2) qubits[60];
cz qubits[56],qubits[24];
rx(pi/2) qubits[6];
ry(pi/2) qubits[53];
t qubits[28];
t qubits[12];
cz qubits[13],qubits[53];
ry(pi/2) qubits[63];
z qubits[21];
h qubits[41];
ry(pi/2) qubits[40];
y qubits[10];
s qubits[0];
t qubits[51];
s qubits[65];
z qubits[16];
ry(pi/2) qubits[8];
cx qubits[0],qubits[37];
ry(pi/2) qubits[16];
s qubits[65];
z qubits[0];
cz qubits[23],qubits[57];
z qubits[53];
cx qubits[35],qubits[36];
t qubits[5];
y qubits[46];
t qubits[40];
rx(pi/2) qubits[12];
s qubits[49];
t qubits[46];
y qubits[16];
z qubits[66];
s qubits[16];
rx(pi/2) qubits[3];
ry(pi/2) qubits[40];
cz qubits[21],qubits[5];
s qubits[35];
x qubits[35];
cz qubits[49],qubits[1];
ccx qubits[19],qubits[48],qubits[49];
ccx qubits[43],qubits[3],qubits[31];
cx qubits[12],qubits[19];
cx qubits[40],qubits[65];
cz qubits[36],qubits[11];
t qubits[51];
ccx qubits[10],qubits[8],qubits[56];
ry(pi/2) qubits[23];
cx qubits[29],qubits[59];
rx(pi/2) qubits[20];
ry(pi/2) qubits[52];
h qubits[50];
cz qubits[54],qubits[24];
rx(pi/2) qubits[15];
y qubits[59];
y qubits[19];
cx qubits[42],qubits[35];
z qubits[65];
x qubits[58];
z qubits[3];
t qubits[17];
t qubits[32];
y qubits[2];
cz qubits[28],qubits[35];
rx(pi/2) qubits[10];
ry(pi/2) qubits[28];
ccx qubits[1],qubits[64],qubits[31];
y qubits[65];
ry(pi/2) qubits[5];
cx qubits[61],qubits[59];
h qubits[69];
z qubits[42];
ccx qubits[16],qubits[58],qubits[8];