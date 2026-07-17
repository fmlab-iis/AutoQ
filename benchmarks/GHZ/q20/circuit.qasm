OPENQASM 3.0;
include "stdgates.inc";
qubit[20] qb;
bit[20] outcome;

h qb[0];
h qb[1];
h qb[2];
h qb[3];
h qb[4];
h qb[5];
h qb[6];
h qb[7];
h qb[8];
h qb[9];
h qb[10];
h qb[11];
h qb[12];
h qb[13];
h qb[14];
h qb[15];
h qb[16];
h qb[17];
h qb[18];
h qb[19];

cz qb[1], qb[2];
cz qb[3], qb[4];
cz qb[5], qb[6];
cz qb[7], qb[8];
cz qb[9], qb[10];
cz qb[11], qb[12];
cz qb[13], qb[14];
cz qb[15], qb[16];
cz qb[17], qb[18];

cz qb[0], qb[1];
cz qb[2], qb[3];
cz qb[4], qb[5];
cz qb[6], qb[7];
cz qb[8], qb[9];
cz qb[10], qb[11];
cz qb[12], qb[13];
cz qb[14], qb[15];
cz qb[16], qb[17];
cz qb[18], qb[19];

h qb[1];
h qb[3];
h qb[5];
h qb[7];
h qb[9];
h qb[11];
h qb[13];
h qb[15];
h qb[17];
h qb[19];

outcome[1] = measure qb[1];
if (!outcome[1]) {
    cx qb[1], qb[2];
}
else {
    cx qb[1], qb[2];
    x qb[1];
}

outcome[3] = measure qb[3];
if (!outcome[3]) {
    cx qb[3], qb[4];
}
else {
    cx qb[3], qb[4];
    x qb[3];
}

outcome[5] = measure qb[5];
if (!outcome[5]) {
    cx qb[5], qb[6];
}
else {
    cx qb[5], qb[6];
    x qb[5];
}

outcome[7] = measure qb[7];
if (!outcome[7]) {
    cx qb[7], qb[8];
}
else {
    cx qb[7], qb[8];
    x qb[7];
}

outcome[9] = measure qb[9];
if (!outcome[9]) {
    cx qb[9], qb[10];
}
else {
    cx qb[9], qb[10];
    x qb[9];
}

outcome[11] = measure qb[11];
if (!outcome[11]) {
    cx qb[11], qb[12];
}
else {
    cx qb[11], qb[12];
    x qb[11];
}

outcome[13] = measure qb[13];
if (!outcome[13]) {
    cx qb[13], qb[14];
}
else {
    cx qb[13], qb[14];
    x qb[13];
}

outcome[15] = measure qb[15];
if (!outcome[15]) {
    cx qb[15], qb[16];
}
else {
    cx qb[15], qb[16];
    x qb[15];
}

outcome[17] = measure qb[17];
if (!outcome[17]) {
    cx qb[17], qb[18];
}
else {
    cx qb[17], qb[18];
    x qb[17];
}

outcome[19] = measure qb[19];
if (!outcome[19]) {
    cx qb[19], qb[20];
}
else {
    cx qb[19], qb[20];
    x qb[19];
}

cx qb[2], qb[1];
cx qb[4], qb[3];
cx qb[6], qb[5];
cx qb[8], qb[7];
cx qb[10], qb[9];
cx qb[12], qb[11];
cx qb[14], qb[13];
cx qb[16], qb[15];
cx qb[18], qb[17];
