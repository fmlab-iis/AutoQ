OPENQASM 3.0;
include "stdgates.inc";
qubit[3] qb;
bit[1] outcome;

h qb[0];
h qb[1];
h qb[2];

cz qb[1], qb[2];

cz qb[0], qb[1];

h qb[1];

outcome[0] = measure qb[1];
if (!outcome[0]) {
    cx qb[1], qb[2];
}
else {
    cx qb[1], qb[2];
    x qb[1];
}

cx qb[2], qb[1];
