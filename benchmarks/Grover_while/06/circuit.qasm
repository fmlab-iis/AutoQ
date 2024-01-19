OPENQASM 3;
include "stdgates.inc";
qubit[13] qb;
bit[13] outcome;

// Define a controlled U operation using the ctrl gate modifier.
// q1 is control, q2 is target
gate custom q {
    U(0.190332413, 0, 0) q;
}
gate ccustom q1, q2 {
    ctrl @ custom q1, q2;
}

h qb[7];
h qb[8];
h qb[9];
h qb[10];
h qb[11];
h qb[12];
ccx qb[7], qb[8], qb[0];
ccx qb[0], qb[9], qb[1];
ccx qb[1], qb[10], qb[2];
ccx qb[2], qb[11], qb[3];
ccx qb[3], qb[12], qb[4];
cx qb[4], qb[6];
ccx qb[3], qb[12], qb[4];
ccx qb[2], qb[11], qb[3];
ccx qb[1], qb[10], qb[2];
ccx qb[0], qb[9], qb[1];
ccx qb[7], qb[8], qb[0];
ccustom qb[6], qb[5];
ccx qb[7], qb[8], qb[0];
ccx qb[0], qb[9], qb[1];
ccx qb[1], qb[10], qb[2];
ccx qb[2], qb[11], qb[3];
ccx qb[3], qb[12], qb[4];
cx qb[4], qb[6];
ccx qb[3], qb[12], qb[4];
ccx qb[2], qb[11], qb[3];
ccx qb[1], qb[10], qb[2];
ccx qb[0], qb[9], qb[1];
ccx qb[7], qb[8], qb[0];

outcome[5] = measure qb[5];
while (!outcome[5]) { // loop-invariant.spec
x qb[6];
h qb[6];
ccx qb[7], qb[8], qb[0];
ccx qb[0], qb[9], qb[1];
ccx qb[1], qb[10], qb[2];
ccx qb[2], qb[11], qb[3];
ccx qb[3], qb[12], qb[4];
cx qb[4], qb[6];
ccx qb[3], qb[12], qb[4];
ccx qb[2], qb[11], qb[3];
ccx qb[1], qb[10], qb[2];
ccx qb[0], qb[9], qb[1];
ccx qb[7], qb[8], qb[0];
h qb[6];
x qb[6];
h qb[7];
h qb[8];
h qb[9];
h qb[10];
h qb[11];
h qb[12];
x qb[7];
x qb[8];
x qb[9];
x qb[10];
x qb[11];
x qb[12];
ccx qb[7], qb[8], qb[0];
ccx qb[0], qb[9], qb[1];
ccx qb[1], qb[10], qb[2];
ccx qb[2], qb[11], qb[3];
cz qb[3], qb[12];
ccx qb[2], qb[11], qb[3];
ccx qb[1], qb[10], qb[2];
ccx qb[0], qb[9], qb[1];
ccx qb[7], qb[8], qb[0];
x qb[7];
x qb[8];
x qb[9];
x qb[10];
x qb[11];
x qb[12];
h qb[7];
h qb[8];
h qb[9];
h qb[10];
h qb[11];
h qb[12];
ccx qb[7], qb[8], qb[0];
ccx qb[0], qb[9], qb[1];
ccx qb[1], qb[10], qb[2];
ccx qb[2], qb[11], qb[3];
ccx qb[3], qb[12], qb[4];
cx qb[4], qb[6];
ccx qb[3], qb[12], qb[4];
ccx qb[2], qb[11], qb[3];
ccx qb[1], qb[10], qb[2];
ccx qb[0], qb[9], qb[1];
ccx qb[7], qb[8], qb[0];
ccustom qb[6], qb[5];
ccx qb[7], qb[8], qb[0];
ccx qb[0], qb[9], qb[1];
ccx qb[1], qb[10], qb[2];
ccx qb[2], qb[11], qb[3];
ccx qb[3], qb[12], qb[4];
cx qb[4], qb[6];
ccx qb[3], qb[12], qb[4];
ccx qb[2], qb[11], qb[3];
ccx qb[1], qb[10], qb[2];
ccx qb[0], qb[9], qb[1];
ccx qb[7], qb[8], qb[0];
outcome[5] = measure qb[5];
} // post.spec

// outcome = measure qb;
