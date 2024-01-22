OPENQASM 3;
include "stdgates.inc";
qubit[2] qb;
bit[2] outcome;

h qb[0];
cx qb[0], qb[1];
outcome[0] = measure qb[0];
while (!outcome[0]) { // loop-invariant.hsl
    x qb[0];
    h qb[0];
    cx qb[0], qb[1];
    outcome[0] = measure qb[0];
} // post.hsl