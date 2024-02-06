OPENQASM 3;
include "stdgates.inc";
qubit[1] qb;
bit[1] outcome;

outcome[0] = measure qb[0];
while (!outcome[0]) { // loop-invariant.hsl
    h qb[0];
    h qb[0];
    outcome[0] = measure qb[0];
}
