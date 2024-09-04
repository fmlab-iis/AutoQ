OPENQASM 3;
include "stdgates.inc";
qubit[99] qb;
bit[99] outcome;

/******************************************************/
// Users should be notified that all gate definitions
// in this circuit file are simply ignored by AutoQ 2.0.
// These definitions are intended for this circuit file
// to be readable by qiskit.
gate k q {
    U(0.190332413, 0, 0) q;
}
gate ck q1, q2 {
    ctrl @ k q1, q2;
}
/******************************************************/

h qb[50];
h qb[51];
h qb[52];
h qb[53];
h qb[54];
h qb[55];
h qb[56];
h qb[57];
h qb[58];
h qb[59];
h qb[60];
h qb[61];
h qb[62];
h qb[63];
h qb[64];
h qb[65];
h qb[66];
h qb[67];
h qb[68];
h qb[69];
h qb[70];
h qb[71];
h qb[72];
h qb[73];
h qb[74];
h qb[75];
h qb[76];
h qb[77];
h qb[78];
h qb[79];
h qb[80];
h qb[81];
h qb[82];
h qb[83];
h qb[84];
h qb[85];
h qb[86];
h qb[87];
h qb[88];
h qb[89];
h qb[90];
h qb[91];
h qb[92];
h qb[93];
h qb[94];
h qb[95];
h qb[96];
h qb[97];
h qb[98];
ccx qb[50], qb[51], qb[0];
ccx qb[0], qb[52], qb[1];
ccx qb[1], qb[53], qb[2];
ccx qb[2], qb[54], qb[3];
ccx qb[3], qb[55], qb[4];
ccx qb[4], qb[56], qb[5];
ccx qb[5], qb[57], qb[6];
ccx qb[6], qb[58], qb[7];
ccx qb[7], qb[59], qb[8];
ccx qb[8], qb[60], qb[9];
ccx qb[9], qb[61], qb[10];
ccx qb[10], qb[62], qb[11];
ccx qb[11], qb[63], qb[12];
ccx qb[12], qb[64], qb[13];
ccx qb[13], qb[65], qb[14];
ccx qb[14], qb[66], qb[15];
ccx qb[15], qb[67], qb[16];
ccx qb[16], qb[68], qb[17];
ccx qb[17], qb[69], qb[18];
ccx qb[18], qb[70], qb[19];
ccx qb[19], qb[71], qb[20];
ccx qb[20], qb[72], qb[21];
ccx qb[21], qb[73], qb[22];
ccx qb[22], qb[74], qb[23];
ccx qb[23], qb[75], qb[24];
ccx qb[24], qb[76], qb[25];
ccx qb[25], qb[77], qb[26];
ccx qb[26], qb[78], qb[27];
ccx qb[27], qb[79], qb[28];
ccx qb[28], qb[80], qb[29];
ccx qb[29], qb[81], qb[30];
ccx qb[30], qb[82], qb[31];
ccx qb[31], qb[83], qb[32];
ccx qb[32], qb[84], qb[33];
ccx qb[33], qb[85], qb[34];
ccx qb[34], qb[86], qb[35];
ccx qb[35], qb[87], qb[36];
ccx qb[36], qb[88], qb[37];
ccx qb[37], qb[89], qb[38];
ccx qb[38], qb[90], qb[39];
ccx qb[39], qb[91], qb[40];
ccx qb[40], qb[92], qb[41];
ccx qb[41], qb[93], qb[42];
ccx qb[42], qb[94], qb[43];
ccx qb[43], qb[95], qb[44];
ccx qb[44], qb[96], qb[45];
ccx qb[45], qb[97], qb[46];
ccx qb[46], qb[98], qb[47];
cx qb[47], qb[49];
ccx qb[46], qb[98], qb[47];
ccx qb[45], qb[97], qb[46];
ccx qb[44], qb[96], qb[45];
ccx qb[43], qb[95], qb[44];
ccx qb[42], qb[94], qb[43];
ccx qb[41], qb[93], qb[42];
ccx qb[40], qb[92], qb[41];
ccx qb[39], qb[91], qb[40];
ccx qb[38], qb[90], qb[39];
ccx qb[37], qb[89], qb[38];
ccx qb[36], qb[88], qb[37];
ccx qb[35], qb[87], qb[36];
ccx qb[34], qb[86], qb[35];
ccx qb[33], qb[85], qb[34];
ccx qb[32], qb[84], qb[33];
ccx qb[31], qb[83], qb[32];
ccx qb[30], qb[82], qb[31];
ccx qb[29], qb[81], qb[30];
ccx qb[28], qb[80], qb[29];
ccx qb[27], qb[79], qb[28];
ccx qb[26], qb[78], qb[27];
ccx qb[25], qb[77], qb[26];
ccx qb[24], qb[76], qb[25];
ccx qb[23], qb[75], qb[24];
ccx qb[22], qb[74], qb[23];
ccx qb[21], qb[73], qb[22];
ccx qb[20], qb[72], qb[21];
ccx qb[19], qb[71], qb[20];
ccx qb[18], qb[70], qb[19];
ccx qb[17], qb[69], qb[18];
ccx qb[16], qb[68], qb[17];
ccx qb[15], qb[67], qb[16];
ccx qb[14], qb[66], qb[15];
ccx qb[13], qb[65], qb[14];
ccx qb[12], qb[64], qb[13];
ccx qb[11], qb[63], qb[12];
ccx qb[10], qb[62], qb[11];
ccx qb[9], qb[61], qb[10];
ccx qb[8], qb[60], qb[9];
ccx qb[7], qb[59], qb[8];
ccx qb[6], qb[58], qb[7];
ccx qb[5], qb[57], qb[6];
ccx qb[4], qb[56], qb[5];
ccx qb[3], qb[55], qb[4];
ccx qb[2], qb[54], qb[3];
ccx qb[1], qb[53], qb[2];
ccx qb[0], qb[52], qb[1];
ccx qb[50], qb[51], qb[0];
ck qb[49], qb[48];
ccx qb[50], qb[51], qb[0];
ccx qb[0], qb[52], qb[1];
ccx qb[1], qb[53], qb[2];
ccx qb[2], qb[54], qb[3];
ccx qb[3], qb[55], qb[4];
ccx qb[4], qb[56], qb[5];
ccx qb[5], qb[57], qb[6];
ccx qb[6], qb[58], qb[7];
ccx qb[7], qb[59], qb[8];
ccx qb[8], qb[60], qb[9];
ccx qb[9], qb[61], qb[10];
ccx qb[10], qb[62], qb[11];
ccx qb[11], qb[63], qb[12];
ccx qb[12], qb[64], qb[13];
ccx qb[13], qb[65], qb[14];
ccx qb[14], qb[66], qb[15];
ccx qb[15], qb[67], qb[16];
ccx qb[16], qb[68], qb[17];
ccx qb[17], qb[69], qb[18];
ccx qb[18], qb[70], qb[19];
ccx qb[19], qb[71], qb[20];
ccx qb[20], qb[72], qb[21];
ccx qb[21], qb[73], qb[22];
ccx qb[22], qb[74], qb[23];
ccx qb[23], qb[75], qb[24];
ccx qb[24], qb[76], qb[25];
ccx qb[25], qb[77], qb[26];
ccx qb[26], qb[78], qb[27];
ccx qb[27], qb[79], qb[28];
ccx qb[28], qb[80], qb[29];
ccx qb[29], qb[81], qb[30];
ccx qb[30], qb[82], qb[31];
ccx qb[31], qb[83], qb[32];
ccx qb[32], qb[84], qb[33];
ccx qb[33], qb[85], qb[34];
ccx qb[34], qb[86], qb[35];
ccx qb[35], qb[87], qb[36];
ccx qb[36], qb[88], qb[37];
ccx qb[37], qb[89], qb[38];
ccx qb[38], qb[90], qb[39];
ccx qb[39], qb[91], qb[40];
ccx qb[40], qb[92], qb[41];
ccx qb[41], qb[93], qb[42];
ccx qb[42], qb[94], qb[43];
ccx qb[43], qb[95], qb[44];
ccx qb[44], qb[96], qb[45];
ccx qb[45], qb[97], qb[46];
ccx qb[46], qb[98], qb[47];
cx qb[47], qb[49];
ccx qb[46], qb[98], qb[47];
ccx qb[45], qb[97], qb[46];
ccx qb[44], qb[96], qb[45];
ccx qb[43], qb[95], qb[44];
ccx qb[42], qb[94], qb[43];
ccx qb[41], qb[93], qb[42];
ccx qb[40], qb[92], qb[41];
ccx qb[39], qb[91], qb[40];
ccx qb[38], qb[90], qb[39];
ccx qb[37], qb[89], qb[38];
ccx qb[36], qb[88], qb[37];
ccx qb[35], qb[87], qb[36];
ccx qb[34], qb[86], qb[35];
ccx qb[33], qb[85], qb[34];
ccx qb[32], qb[84], qb[33];
ccx qb[31], qb[83], qb[32];
ccx qb[30], qb[82], qb[31];
ccx qb[29], qb[81], qb[30];
ccx qb[28], qb[80], qb[29];
ccx qb[27], qb[79], qb[28];
ccx qb[26], qb[78], qb[27];
ccx qb[25], qb[77], qb[26];
ccx qb[24], qb[76], qb[25];
ccx qb[23], qb[75], qb[24];
ccx qb[22], qb[74], qb[23];
ccx qb[21], qb[73], qb[22];
ccx qb[20], qb[72], qb[21];
ccx qb[19], qb[71], qb[20];
ccx qb[18], qb[70], qb[19];
ccx qb[17], qb[69], qb[18];
ccx qb[16], qb[68], qb[17];
ccx qb[15], qb[67], qb[16];
ccx qb[14], qb[66], qb[15];
ccx qb[13], qb[65], qb[14];
ccx qb[12], qb[64], qb[13];
ccx qb[11], qb[63], qb[12];
ccx qb[10], qb[62], qb[11];
ccx qb[9], qb[61], qb[10];
ccx qb[8], qb[60], qb[9];
ccx qb[7], qb[59], qb[8];
ccx qb[6], qb[58], qb[7];
ccx qb[5], qb[57], qb[6];
ccx qb[4], qb[56], qb[5];
ccx qb[3], qb[55], qb[4];
ccx qb[2], qb[54], qb[3];
ccx qb[1], qb[53], qb[2];
ccx qb[0], qb[52], qb[1];
ccx qb[50], qb[51], qb[0];

outcome[48] = measure qb[48];
while (!outcome[48]) { // loop-invariant.spec
x qb[49];
h qb[49];
ccx qb[50], qb[51], qb[0];
ccx qb[0], qb[52], qb[1];
ccx qb[1], qb[53], qb[2];
ccx qb[2], qb[54], qb[3];
ccx qb[3], qb[55], qb[4];
ccx qb[4], qb[56], qb[5];
ccx qb[5], qb[57], qb[6];
ccx qb[6], qb[58], qb[7];
ccx qb[7], qb[59], qb[8];
ccx qb[8], qb[60], qb[9];
ccx qb[9], qb[61], qb[10];
ccx qb[10], qb[62], qb[11];
ccx qb[11], qb[63], qb[12];
ccx qb[12], qb[64], qb[13];
ccx qb[13], qb[65], qb[14];
ccx qb[14], qb[66], qb[15];
ccx qb[15], qb[67], qb[16];
ccx qb[16], qb[68], qb[17];
ccx qb[17], qb[69], qb[18];
ccx qb[18], qb[70], qb[19];
ccx qb[19], qb[71], qb[20];
ccx qb[20], qb[72], qb[21];
ccx qb[21], qb[73], qb[22];
ccx qb[22], qb[74], qb[23];
ccx qb[23], qb[75], qb[24];
ccx qb[24], qb[76], qb[25];
ccx qb[25], qb[77], qb[26];
ccx qb[26], qb[78], qb[27];
ccx qb[27], qb[79], qb[28];
ccx qb[28], qb[80], qb[29];
ccx qb[29], qb[81], qb[30];
ccx qb[30], qb[82], qb[31];
ccx qb[31], qb[83], qb[32];
ccx qb[32], qb[84], qb[33];
ccx qb[33], qb[85], qb[34];
ccx qb[34], qb[86], qb[35];
ccx qb[35], qb[87], qb[36];
ccx qb[36], qb[88], qb[37];
ccx qb[37], qb[89], qb[38];
ccx qb[38], qb[90], qb[39];
ccx qb[39], qb[91], qb[40];
ccx qb[40], qb[92], qb[41];
ccx qb[41], qb[93], qb[42];
ccx qb[42], qb[94], qb[43];
ccx qb[43], qb[95], qb[44];
ccx qb[44], qb[96], qb[45];
ccx qb[45], qb[97], qb[46];
ccx qb[46], qb[98], qb[47];
cx qb[47], qb[49];
ccx qb[46], qb[98], qb[47];
ccx qb[45], qb[97], qb[46];
ccx qb[44], qb[96], qb[45];
ccx qb[43], qb[95], qb[44];
ccx qb[42], qb[94], qb[43];
ccx qb[41], qb[93], qb[42];
ccx qb[40], qb[92], qb[41];
ccx qb[39], qb[91], qb[40];
ccx qb[38], qb[90], qb[39];
ccx qb[37], qb[89], qb[38];
ccx qb[36], qb[88], qb[37];
ccx qb[35], qb[87], qb[36];
ccx qb[34], qb[86], qb[35];
ccx qb[33], qb[85], qb[34];
ccx qb[32], qb[84], qb[33];
ccx qb[31], qb[83], qb[32];
ccx qb[30], qb[82], qb[31];
ccx qb[29], qb[81], qb[30];
ccx qb[28], qb[80], qb[29];
ccx qb[27], qb[79], qb[28];
ccx qb[26], qb[78], qb[27];
ccx qb[25], qb[77], qb[26];
ccx qb[24], qb[76], qb[25];
ccx qb[23], qb[75], qb[24];
ccx qb[22], qb[74], qb[23];
ccx qb[21], qb[73], qb[22];
ccx qb[20], qb[72], qb[21];
ccx qb[19], qb[71], qb[20];
ccx qb[18], qb[70], qb[19];
ccx qb[17], qb[69], qb[18];
ccx qb[16], qb[68], qb[17];
ccx qb[15], qb[67], qb[16];
ccx qb[14], qb[66], qb[15];
ccx qb[13], qb[65], qb[14];
ccx qb[12], qb[64], qb[13];
ccx qb[11], qb[63], qb[12];
ccx qb[10], qb[62], qb[11];
ccx qb[9], qb[61], qb[10];
ccx qb[8], qb[60], qb[9];
ccx qb[7], qb[59], qb[8];
ccx qb[6], qb[58], qb[7];
ccx qb[5], qb[57], qb[6];
ccx qb[4], qb[56], qb[5];
ccx qb[3], qb[55], qb[4];
ccx qb[2], qb[54], qb[3];
ccx qb[1], qb[53], qb[2];
ccx qb[0], qb[52], qb[1];
ccx qb[50], qb[51], qb[0];
h qb[49];
x qb[49];
h qb[50];
h qb[51];
h qb[52];
h qb[53];
h qb[54];
h qb[55];
h qb[56];
h qb[57];
h qb[58];
h qb[59];
h qb[60];
h qb[61];
h qb[62];
h qb[63];
h qb[64];
h qb[65];
h qb[66];
h qb[67];
h qb[68];
h qb[69];
h qb[70];
h qb[71];
h qb[72];
h qb[73];
h qb[74];
h qb[75];
h qb[76];
h qb[77];
h qb[78];
h qb[79];
h qb[80];
h qb[81];
h qb[82];
h qb[83];
h qb[84];
h qb[85];
h qb[86];
h qb[87];
h qb[88];
h qb[89];
h qb[90];
h qb[91];
h qb[92];
h qb[93];
h qb[94];
h qb[95];
h qb[96];
h qb[97];
h qb[98];
x qb[50];
x qb[51];
x qb[52];
x qb[53];
x qb[54];
x qb[55];
x qb[56];
x qb[57];
x qb[58];
x qb[59];
x qb[60];
x qb[61];
x qb[62];
x qb[63];
x qb[64];
x qb[65];
x qb[66];
x qb[67];
x qb[68];
x qb[69];
x qb[70];
x qb[71];
x qb[72];
x qb[73];
x qb[74];
x qb[75];
x qb[76];
x qb[77];
x qb[78];
x qb[79];
x qb[80];
x qb[81];
x qb[82];
x qb[83];
x qb[84];
x qb[85];
x qb[86];
x qb[87];
x qb[88];
x qb[89];
x qb[90];
x qb[91];
x qb[92];
x qb[93];
x qb[94];
x qb[95];
x qb[96];
x qb[97];
x qb[98];
ccx qb[50], qb[51], qb[0];
ccx qb[0], qb[52], qb[1];
ccx qb[1], qb[53], qb[2];
ccx qb[2], qb[54], qb[3];
ccx qb[3], qb[55], qb[4];
ccx qb[4], qb[56], qb[5];
ccx qb[5], qb[57], qb[6];
ccx qb[6], qb[58], qb[7];
ccx qb[7], qb[59], qb[8];
ccx qb[8], qb[60], qb[9];
ccx qb[9], qb[61], qb[10];
ccx qb[10], qb[62], qb[11];
ccx qb[11], qb[63], qb[12];
ccx qb[12], qb[64], qb[13];
ccx qb[13], qb[65], qb[14];
ccx qb[14], qb[66], qb[15];
ccx qb[15], qb[67], qb[16];
ccx qb[16], qb[68], qb[17];
ccx qb[17], qb[69], qb[18];
ccx qb[18], qb[70], qb[19];
ccx qb[19], qb[71], qb[20];
ccx qb[20], qb[72], qb[21];
ccx qb[21], qb[73], qb[22];
ccx qb[22], qb[74], qb[23];
ccx qb[23], qb[75], qb[24];
ccx qb[24], qb[76], qb[25];
ccx qb[25], qb[77], qb[26];
ccx qb[26], qb[78], qb[27];
ccx qb[27], qb[79], qb[28];
ccx qb[28], qb[80], qb[29];
ccx qb[29], qb[81], qb[30];
ccx qb[30], qb[82], qb[31];
ccx qb[31], qb[83], qb[32];
ccx qb[32], qb[84], qb[33];
ccx qb[33], qb[85], qb[34];
ccx qb[34], qb[86], qb[35];
ccx qb[35], qb[87], qb[36];
ccx qb[36], qb[88], qb[37];
ccx qb[37], qb[89], qb[38];
ccx qb[38], qb[90], qb[39];
ccx qb[39], qb[91], qb[40];
ccx qb[40], qb[92], qb[41];
ccx qb[41], qb[93], qb[42];
ccx qb[42], qb[94], qb[43];
ccx qb[43], qb[95], qb[44];
ccx qb[44], qb[96], qb[45];
ccx qb[45], qb[97], qb[46];
cz qb[46], qb[98];
ccx qb[45], qb[97], qb[46];
ccx qb[44], qb[96], qb[45];
ccx qb[43], qb[95], qb[44];
ccx qb[42], qb[94], qb[43];
ccx qb[41], qb[93], qb[42];
ccx qb[40], qb[92], qb[41];
ccx qb[39], qb[91], qb[40];
ccx qb[38], qb[90], qb[39];
ccx qb[37], qb[89], qb[38];
ccx qb[36], qb[88], qb[37];
ccx qb[35], qb[87], qb[36];
ccx qb[34], qb[86], qb[35];
ccx qb[33], qb[85], qb[34];
ccx qb[32], qb[84], qb[33];
ccx qb[31], qb[83], qb[32];
ccx qb[30], qb[82], qb[31];
ccx qb[29], qb[81], qb[30];
ccx qb[28], qb[80], qb[29];
ccx qb[27], qb[79], qb[28];
ccx qb[26], qb[78], qb[27];
ccx qb[25], qb[77], qb[26];
ccx qb[24], qb[76], qb[25];
ccx qb[23], qb[75], qb[24];
ccx qb[22], qb[74], qb[23];
ccx qb[21], qb[73], qb[22];
ccx qb[20], qb[72], qb[21];
ccx qb[19], qb[71], qb[20];
ccx qb[18], qb[70], qb[19];
ccx qb[17], qb[69], qb[18];
ccx qb[16], qb[68], qb[17];
ccx qb[15], qb[67], qb[16];
ccx qb[14], qb[66], qb[15];
ccx qb[13], qb[65], qb[14];
ccx qb[12], qb[64], qb[13];
ccx qb[11], qb[63], qb[12];
ccx qb[10], qb[62], qb[11];
ccx qb[9], qb[61], qb[10];
ccx qb[8], qb[60], qb[9];
ccx qb[7], qb[59], qb[8];
ccx qb[6], qb[58], qb[7];
ccx qb[5], qb[57], qb[6];
ccx qb[4], qb[56], qb[5];
ccx qb[3], qb[55], qb[4];
ccx qb[2], qb[54], qb[3];
ccx qb[1], qb[53], qb[2];
ccx qb[0], qb[52], qb[1];
ccx qb[50], qb[51], qb[0];
x qb[50];
x qb[51];
x qb[52];
x qb[53];
x qb[54];
x qb[55];
x qb[56];
x qb[57];
x qb[58];
x qb[59];
x qb[60];
x qb[61];
x qb[62];
x qb[63];
x qb[64];
x qb[65];
x qb[66];
x qb[67];
x qb[68];
x qb[69];
x qb[70];
x qb[71];
x qb[72];
x qb[73];
x qb[74];
x qb[75];
x qb[76];
x qb[77];
x qb[78];
x qb[79];
x qb[80];
x qb[81];
x qb[82];
x qb[83];
x qb[84];
x qb[85];
x qb[86];
x qb[87];
x qb[88];
x qb[89];
x qb[90];
x qb[91];
x qb[92];
x qb[93];
x qb[94];
x qb[95];
x qb[96];
x qb[97];
x qb[98];
h qb[50];
h qb[51];
h qb[52];
h qb[53];
h qb[54];
h qb[55];
h qb[56];
h qb[57];
h qb[58];
h qb[59];
h qb[60];
h qb[61];
h qb[62];
h qb[63];
h qb[64];
h qb[65];
h qb[66];
h qb[67];
h qb[68];
h qb[69];
h qb[70];
h qb[71];
h qb[72];
h qb[73];
h qb[74];
h qb[75];
h qb[76];
h qb[77];
h qb[78];
h qb[79];
h qb[80];
h qb[81];
h qb[82];
h qb[83];
h qb[84];
h qb[85];
h qb[86];
h qb[87];
h qb[88];
h qb[89];
h qb[90];
h qb[91];
h qb[92];
h qb[93];
h qb[94];
h qb[95];
h qb[96];
h qb[97];
h qb[98];
ccx qb[50], qb[51], qb[0];
ccx qb[0], qb[52], qb[1];
ccx qb[1], qb[53], qb[2];
ccx qb[2], qb[54], qb[3];
ccx qb[3], qb[55], qb[4];
ccx qb[4], qb[56], qb[5];
ccx qb[5], qb[57], qb[6];
ccx qb[6], qb[58], qb[7];
ccx qb[7], qb[59], qb[8];
ccx qb[8], qb[60], qb[9];
ccx qb[9], qb[61], qb[10];
ccx qb[10], qb[62], qb[11];
ccx qb[11], qb[63], qb[12];
ccx qb[12], qb[64], qb[13];
ccx qb[13], qb[65], qb[14];
ccx qb[14], qb[66], qb[15];
ccx qb[15], qb[67], qb[16];
ccx qb[16], qb[68], qb[17];
ccx qb[17], qb[69], qb[18];
ccx qb[18], qb[70], qb[19];
ccx qb[19], qb[71], qb[20];
ccx qb[20], qb[72], qb[21];
ccx qb[21], qb[73], qb[22];
ccx qb[22], qb[74], qb[23];
ccx qb[23], qb[75], qb[24];
ccx qb[24], qb[76], qb[25];
ccx qb[25], qb[77], qb[26];
ccx qb[26], qb[78], qb[27];
ccx qb[27], qb[79], qb[28];
ccx qb[28], qb[80], qb[29];
ccx qb[29], qb[81], qb[30];
ccx qb[30], qb[82], qb[31];
ccx qb[31], qb[83], qb[32];
ccx qb[32], qb[84], qb[33];
ccx qb[33], qb[85], qb[34];
ccx qb[34], qb[86], qb[35];
ccx qb[35], qb[87], qb[36];
ccx qb[36], qb[88], qb[37];
ccx qb[37], qb[89], qb[38];
ccx qb[38], qb[90], qb[39];
ccx qb[39], qb[91], qb[40];
ccx qb[40], qb[92], qb[41];
ccx qb[41], qb[93], qb[42];
ccx qb[42], qb[94], qb[43];
ccx qb[43], qb[95], qb[44];
ccx qb[44], qb[96], qb[45];
ccx qb[45], qb[97], qb[46];
ccx qb[46], qb[98], qb[47];
cx qb[47], qb[49];
ccx qb[46], qb[98], qb[47];
ccx qb[45], qb[97], qb[46];
ccx qb[44], qb[96], qb[45];
ccx qb[43], qb[95], qb[44];
ccx qb[42], qb[94], qb[43];
ccx qb[41], qb[93], qb[42];
ccx qb[40], qb[92], qb[41];
ccx qb[39], qb[91], qb[40];
ccx qb[38], qb[90], qb[39];
ccx qb[37], qb[89], qb[38];
ccx qb[36], qb[88], qb[37];
ccx qb[35], qb[87], qb[36];
ccx qb[34], qb[86], qb[35];
ccx qb[33], qb[85], qb[34];
ccx qb[32], qb[84], qb[33];
ccx qb[31], qb[83], qb[32];
ccx qb[30], qb[82], qb[31];
ccx qb[29], qb[81], qb[30];
ccx qb[28], qb[80], qb[29];
ccx qb[27], qb[79], qb[28];
ccx qb[26], qb[78], qb[27];
ccx qb[25], qb[77], qb[26];
ccx qb[24], qb[76], qb[25];
ccx qb[23], qb[75], qb[24];
ccx qb[22], qb[74], qb[23];
ccx qb[21], qb[73], qb[22];
ccx qb[20], qb[72], qb[21];
ccx qb[19], qb[71], qb[20];
ccx qb[18], qb[70], qb[19];
ccx qb[17], qb[69], qb[18];
ccx qb[16], qb[68], qb[17];
ccx qb[15], qb[67], qb[16];
ccx qb[14], qb[66], qb[15];
ccx qb[13], qb[65], qb[14];
ccx qb[12], qb[64], qb[13];
ccx qb[11], qb[63], qb[12];
ccx qb[10], qb[62], qb[11];
ccx qb[9], qb[61], qb[10];
ccx qb[8], qb[60], qb[9];
ccx qb[7], qb[59], qb[8];
ccx qb[6], qb[58], qb[7];
ccx qb[5], qb[57], qb[6];
ccx qb[4], qb[56], qb[5];
ccx qb[3], qb[55], qb[4];
ccx qb[2], qb[54], qb[3];
ccx qb[1], qb[53], qb[2];
ccx qb[0], qb[52], qb[1];
ccx qb[50], qb[51], qb[0];
ck qb[49], qb[48];
ccx qb[50], qb[51], qb[0];
ccx qb[0], qb[52], qb[1];
ccx qb[1], qb[53], qb[2];
ccx qb[2], qb[54], qb[3];
ccx qb[3], qb[55], qb[4];
ccx qb[4], qb[56], qb[5];
ccx qb[5], qb[57], qb[6];
ccx qb[6], qb[58], qb[7];
ccx qb[7], qb[59], qb[8];
ccx qb[8], qb[60], qb[9];
ccx qb[9], qb[61], qb[10];
ccx qb[10], qb[62], qb[11];
ccx qb[11], qb[63], qb[12];
ccx qb[12], qb[64], qb[13];
ccx qb[13], qb[65], qb[14];
ccx qb[14], qb[66], qb[15];
ccx qb[15], qb[67], qb[16];
ccx qb[16], qb[68], qb[17];
ccx qb[17], qb[69], qb[18];
ccx qb[18], qb[70], qb[19];
ccx qb[19], qb[71], qb[20];
ccx qb[20], qb[72], qb[21];
ccx qb[21], qb[73], qb[22];
ccx qb[22], qb[74], qb[23];
ccx qb[23], qb[75], qb[24];
ccx qb[24], qb[76], qb[25];
ccx qb[25], qb[77], qb[26];
ccx qb[26], qb[78], qb[27];
ccx qb[27], qb[79], qb[28];
ccx qb[28], qb[80], qb[29];
ccx qb[29], qb[81], qb[30];
ccx qb[30], qb[82], qb[31];
ccx qb[31], qb[83], qb[32];
ccx qb[32], qb[84], qb[33];
ccx qb[33], qb[85], qb[34];
ccx qb[34], qb[86], qb[35];
ccx qb[35], qb[87], qb[36];
ccx qb[36], qb[88], qb[37];
ccx qb[37], qb[89], qb[38];
ccx qb[38], qb[90], qb[39];
ccx qb[39], qb[91], qb[40];
ccx qb[40], qb[92], qb[41];
ccx qb[41], qb[93], qb[42];
ccx qb[42], qb[94], qb[43];
ccx qb[43], qb[95], qb[44];
ccx qb[44], qb[96], qb[45];
ccx qb[45], qb[97], qb[46];
ccx qb[46], qb[98], qb[47];
cx qb[47], qb[49];
ccx qb[46], qb[98], qb[47];
ccx qb[45], qb[97], qb[46];
ccx qb[44], qb[96], qb[45];
ccx qb[43], qb[95], qb[44];
ccx qb[42], qb[94], qb[43];
ccx qb[41], qb[93], qb[42];
ccx qb[40], qb[92], qb[41];
ccx qb[39], qb[91], qb[40];
ccx qb[38], qb[90], qb[39];
ccx qb[37], qb[89], qb[38];
ccx qb[36], qb[88], qb[37];
ccx qb[35], qb[87], qb[36];
ccx qb[34], qb[86], qb[35];
ccx qb[33], qb[85], qb[34];
ccx qb[32], qb[84], qb[33];
ccx qb[31], qb[83], qb[32];
ccx qb[30], qb[82], qb[31];
ccx qb[29], qb[81], qb[30];
ccx qb[28], qb[80], qb[29];
ccx qb[27], qb[79], qb[28];
ccx qb[26], qb[78], qb[27];
ccx qb[25], qb[77], qb[26];
ccx qb[24], qb[76], qb[25];
ccx qb[23], qb[75], qb[24];
ccx qb[22], qb[74], qb[23];
ccx qb[21], qb[73], qb[22];
ccx qb[20], qb[72], qb[21];
ccx qb[19], qb[71], qb[20];
ccx qb[18], qb[70], qb[19];
ccx qb[17], qb[69], qb[18];
ccx qb[16], qb[68], qb[17];
ccx qb[15], qb[67], qb[16];
ccx qb[14], qb[66], qb[15];
ccx qb[13], qb[65], qb[14];
ccx qb[12], qb[64], qb[13];
ccx qb[11], qb[63], qb[12];
ccx qb[10], qb[62], qb[11];
ccx qb[9], qb[61], qb[10];
ccx qb[8], qb[60], qb[9];
ccx qb[7], qb[59], qb[8];
ccx qb[6], qb[58], qb[7];
ccx qb[5], qb[57], qb[6];
ccx qb[4], qb[56], qb[5];
ccx qb[3], qb[55], qb[4];
ccx qb[2], qb[54], qb[3];
ccx qb[1], qb[53], qb[2];
ccx qb[0], qb[52], qb[1];
ccx qb[50], qb[51], qb[0];
outcome[48] = measure qb[48];
}

// outcome = measure qb;