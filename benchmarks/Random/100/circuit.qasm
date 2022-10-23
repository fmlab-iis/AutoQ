OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[100];

cx qubits[56], qubits[33];
z qubits[67];
x qubits[69];
s qubits[60];
x qubits[77];
ry(pi/2) qubits[93];
cx qubits[55], qubits[24];
y qubits[19];
cx qubits[5], qubits[85];
x qubits[41];
h qubits[60];
cz qubits[51], qubits[98];
x qubits[94];
ccx qubits[51], qubits[50], qubits[68];
cz qubits[69], qubits[37];
z qubits[76];
cz qubits[97], qubits[6];
t qubits[42];
z qubits[77];
cx qubits[90], qubits[96];
h qubits[96];
x qubits[61];
h qubits[71];
cx qubits[3], qubits[22];
ccx qubits[2], qubits[68], qubits[7];
t qubits[71];
ry(pi/2) qubits[75];
cz qubits[13], qubits[66];
x qubits[63];
h qubits[23];
ry(pi/2) qubits[6];
t qubits[13];
y qubits[49];
x qubits[19];
x qubits[96];
cx qubits[87], qubits[19];
s qubits[90];
y qubits[26];
x qubits[10];
y qubits[50];
ry(pi/2) qubits[60];
ry(pi/2) qubits[73];
ccx qubits[92], qubits[90], qubits[40];
h qubits[65];
cz qubits[13], qubits[24];
cx qubits[90], qubits[74];
rx(pi/2) qubits[10];
h qubits[52];
rx(pi/2) qubits[58];
h qubits[48];
ry(pi/2) qubits[65];
cz qubits[93], qubits[75];
cx qubits[43], qubits[8];
s qubits[20];
rx(pi/2) qubits[49];
s qubits[76];
h qubits[20];
h qubits[67];
x qubits[66];
ry(pi/2) qubits[76];
t qubits[14];
t qubits[63];
t qubits[32];
y qubits[42];
ry(pi/2) qubits[22];
ccx qubits[59], qubits[15], qubits[34];
ccx qubits[10], qubits[42], qubits[47];
h qubits[27];
z qubits[95];
h qubits[86];
x qubits[45];
rx(pi/2) qubits[1];
ry(pi/2) qubits[15];
rx(pi/2) qubits[55];
z qubits[67];
t qubits[99];
cz qubits[40], qubits[41];
h qubits[15];
z qubits[44];
y qubits[82];
s qubits[93];
ccx qubits[14], qubits[24], qubits[4];
ry(pi/2) qubits[19];
ry(pi/2) qubits[49];
t qubits[56];
s qubits[88];
cx qubits[69], qubits[74];
ry(pi/2) qubits[36];
x qubits[50];
rx(pi/2) qubits[37];
t qubits[72];
s qubits[44];
z qubits[35];
t qubits[83];
z qubits[55];
x qubits[4];
ry(pi/2) qubits[59];
t qubits[70];
t qubits[62];
t qubits[15];
h qubits[98];
z qubits[71];
cx qubits[35], qubits[59];
rx(pi/2) qubits[37];
rx(pi/2) qubits[7];
s qubits[19];
s qubits[76];
t qubits[95];
h qubits[70];
cx qubits[62], qubits[19];
cz qubits[73], qubits[78];
y qubits[95];
t qubits[69];
s qubits[54];
z qubits[73];
z qubits[95];
x qubits[77];
z qubits[68];
cz qubits[53], qubits[75];
h qubits[24];
ry(pi/2) qubits[27];
h qubits[82];
y qubits[81];
ccx qubits[96], qubits[0], qubits[88];
h qubits[31];
ccx qubits[69], qubits[22], qubits[16];
ry(pi/2) qubits[28];
x qubits[68];
x qubits[86];
ccx qubits[96], qubits[93], qubits[86];
ry(pi/2) qubits[98];
ry(pi/2) qubits[65];
x qubits[1];
cz qubits[34], qubits[36];
ccx qubits[16], qubits[45], qubits[76];
t qubits[86];
rx(pi/2) qubits[99];
cz qubits[18], qubits[21];
ry(pi/2) qubits[62];
t qubits[40];
y qubits[20];
ry(pi/2) qubits[49];
s qubits[24];
z qubits[82];
y qubits[1];
cz qubits[97], qubits[3];
t qubits[32];
rx(pi/2) qubits[72];
x qubits[36];
t qubits[68];
ccx qubits[98], qubits[20], qubits[7];
rx(pi/2) qubits[93];
z qubits[30];
rx(pi/2) qubits[49];
ccx qubits[67], qubits[80], qubits[14];
y qubits[4];
x qubits[69];
y qubits[3];
cx qubits[28], qubits[58];
x qubits[12];
h qubits[87];
cz qubits[89], qubits[35];
y qubits[64];
t qubits[52];
cz qubits[2], qubits[98];
y qubits[32];
cx qubits[81], qubits[97];
ry(pi/2) qubits[13];
s qubits[99];
ry(pi/2) qubits[13];
ry(pi/2) qubits[47];
z qubits[42];
t qubits[78];
h qubits[39];
z qubits[95];
y qubits[68];
x qubits[36];
s qubits[68];
s qubits[56];
s qubits[38];
x qubits[55];
t qubits[69];
cz qubits[47], qubits[34];
y qubits[46];
cx qubits[29], qubits[67];
h qubits[97];
t qubits[30];
t qubits[17];
y qubits[6];
x qubits[73];
cx qubits[48], qubits[9];
x qubits[16];
rx(pi/2) qubits[67];
ccx qubits[40], qubits[55], qubits[46];
ry(pi/2) qubits[76];
ry(pi/2) qubits[71];
t qubits[66];
y qubits[65];
h qubits[88];
t qubits[44];
cx qubits[97], qubits[23];
s qubits[67];
cx qubits[84], qubits[40];
s qubits[32];
rx(pi/2) qubits[19];
ry(pi/2) qubits[50];
h qubits[39];
h qubits[45];
s qubits[66];
rx(pi/2) qubits[88];
h qubits[35];
cz qubits[58], qubits[0];
x qubits[47];
t qubits[98];
h qubits[69];
cz qubits[67], qubits[36];
s qubits[3];
t qubits[11];
x qubits[29];
ccx qubits[88], qubits[31], qubits[72];
y qubits[74];
z qubits[17];
ccx qubits[42], qubits[57], qubits[29];
rx(pi/2) qubits[63];
s qubits[29];
y qubits[38];
ccx qubits[16], qubits[87], qubits[70];
t qubits[6];
t qubits[41];
ry(pi/2) qubits[38];
t qubits[97];
rx(pi/2) qubits[39];
z qubits[50];
h qubits[17];
rx(pi/2) qubits[81];
cx qubits[16], qubits[24];
z qubits[45];
h qubits[6];
cx qubits[35], qubits[72];
ry(pi/2) qubits[88];
y qubits[62];
x qubits[78];
cx qubits[16], qubits[71];
z qubits[6];
t qubits[28];
rx(pi/2) qubits[68];
y qubits[75];
cz qubits[35], qubits[52];
ccx qubits[21], qubits[68], qubits[89];
z qubits[66];
x qubits[70];
cz qubits[30], qubits[94];
t qubits[18];
ry(pi/2) qubits[93];
cz qubits[12], qubits[62];
y qubits[36];
x qubits[2];
z qubits[25];
ry(pi/2) qubits[32];
rx(pi/2) qubits[54];
s qubits[78];
ccx qubits[78], qubits[99], qubits[27];
x qubits[15];
ry(pi/2) qubits[62];
z qubits[48];
z qubits[84];
rx(pi/2) qubits[14];
t qubits[71];
cz qubits[83], qubits[85];
ccx qubits[19], qubits[30], qubits[92];
t qubits[56];
t qubits[68];
ccx qubits[26], qubits[33], qubits[78];
cx qubits[11], qubits[29];
y qubits[30];
s qubits[56];
rx(pi/2) qubits[35];
cz qubits[89], qubits[19];
h qubits[4];
rx(pi/2) qubits[6];
h qubits[74];
cz qubits[37], qubits[45];
t qubits[81];
x qubits[30];
h qubits[50];
ry(pi/2) qubits[79];
rx(pi/2) qubits[60];
ry(pi/2) qubits[46];
cx qubits[75], qubits[28];
ccx qubits[83], qubits[73], qubits[21];
ccx qubits[63], qubits[41], qubits[75];
h qubits[31];
h qubits[65];
s qubits[25];
ry(pi/2) qubits[55];
t qubits[36];
x qubits[78];
cx qubits[38], qubits[60];
cz qubits[73], qubits[20];
h qubits[19];