OPENQASM 3;
include "stdgates.inc";
qubit[2] qb;
bit[2] outcome;

h qb[0];
tdg qb[0];
h qb[0];
cz qb[0], qb[1];
h qb[1];
t qb[1];
h qb[1];
tdg qb[1];
h qb[1];
cz qb[0], qb[1];
h qb[0];
tdg qb[0];
h qb[0];
x qb[0];

outcome[0] = measure qb[0];
while (!outcome[0]) { // loop-invariant.aut
h qb[0];
tdg qb[0];
h qb[0];
cz qb[0], qb[1];
h qb[1];
t qb[1];
h qb[1];
tdg qb[1];
h qb[1];
cz qb[0], qb[1];
h qb[0];
tdg qb[0];
h qb[0];
x qb[0];
outcome[0] = measure qb[0];
} // post.aut

// outcome = measure qb;