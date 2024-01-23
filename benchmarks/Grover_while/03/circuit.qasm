OPENQASM 3;
include "stdgates.inc";
qubit[7] qb;
bit[7] outcome;

// Define a controlled U operation using the ctrl gate modifier.
// q1 is control, q2 is target
gate custom q {
    U(0.190332413, 0, 0) q;
}
gate ccustom q1, q2 {
    ctrl @ custom q1, q2;
}

h qb[4];
h qb[5];
h qb[6];
ccx qb[4], qb[5], qb[0];
ccx qb[0], qb[6], qb[1];
cx qb[1], qb[3];
ccx qb[0], qb[6], qb[1];
ccx qb[4], qb[5], qb[0];
ccustom qb[3], qb[2];
ccx qb[4], qb[5], qb[0];
ccx qb[0], qb[6], qb[1];
cx qb[1], qb[3];
ccx qb[0], qb[6], qb[1];
ccx qb[4], qb[5], qb[0];

outcome[2] = measure qb[2];
while (!outcome[2]) { // loop-invariant.spec
x qb[3];
h qb[3];
ccx qb[4], qb[5], qb[0];
ccx qb[0], qb[6], qb[1];
cx qb[1], qb[3];
ccx qb[0], qb[6], qb[1];
ccx qb[4], qb[5], qb[0];
h qb[3];
x qb[3];
h qb[4];
h qb[5];
h qb[6];
x qb[4];
x qb[5];
x qb[6];
ccx qb[4], qb[5], qb[0];
cz qb[0], qb[6];
ccx qb[4], qb[5], qb[0];
x qb[4];
x qb[5];
x qb[6];
h qb[4];
h qb[5];
h qb[6];
ccx qb[4], qb[5], qb[0];
ccx qb[0], qb[6], qb[1];
cx qb[1], qb[3];
ccx qb[0], qb[6], qb[1];
ccx qb[4], qb[5], qb[0];
ccustom qb[3], qb[2];
ccx qb[4], qb[5], qb[0];
ccx qb[0], qb[6], qb[1];
cx qb[1], qb[3];
ccx qb[0], qb[6], qb[1];
ccx qb[4], qb[5], qb[0];
outcome[2] = measure qb[2];
}

// outcome = measure qb;
