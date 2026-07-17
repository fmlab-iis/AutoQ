OPENQASM 3.0;
include "stdgates.inc";
qubit[6] qb;
bit[6] outcome;

h qb[0];
h qb[1];
h qb[2];
h qb[3];
h qb[4];
h qb[5];

cz qb[1], qb[2];
cz qb[3], qb[4];

cz qb[0], qb[1];
cz qb[2], qb[3];
cz qb[4], qb[5];

h qb[1];
h qb[3];
h qb[5];

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

cx qb[2], qb[1];
cx qb[4], qb[3];
