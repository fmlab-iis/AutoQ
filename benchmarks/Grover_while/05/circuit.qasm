OPENQASM 3;
include "stdgates.inc";
qubit[11] qb;
bit[11] outcome;

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

h qb[6];
h qb[7];
h qb[8];
h qb[9];
h qb[10];
ccx qb[6], qb[7], qb[0];
ccx qb[0], qb[8], qb[1];
ccx qb[1], qb[9], qb[2];
ccx qb[2], qb[10], qb[3];
cx qb[3], qb[5];
ccx qb[2], qb[10], qb[3];
ccx qb[1], qb[9], qb[2];
ccx qb[0], qb[8], qb[1];
ccx qb[6], qb[7], qb[0];
ck qb[5], qb[4];
ccx qb[6], qb[7], qb[0];
ccx qb[0], qb[8], qb[1];
ccx qb[1], qb[9], qb[2];
ccx qb[2], qb[10], qb[3];
cx qb[3], qb[5];
ccx qb[2], qb[10], qb[3];
ccx qb[1], qb[9], qb[2];
ccx qb[0], qb[8], qb[1];
ccx qb[6], qb[7], qb[0];

outcome[4] = measure qb[4];
while (!outcome[4]) { // loop-invariant.spec
x qb[5];
h qb[5];
ccx qb[6], qb[7], qb[0];
ccx qb[0], qb[8], qb[1];
ccx qb[1], qb[9], qb[2];
ccx qb[2], qb[10], qb[3];
cx qb[3], qb[5];
ccx qb[2], qb[10], qb[3];
ccx qb[1], qb[9], qb[2];
ccx qb[0], qb[8], qb[1];
ccx qb[6], qb[7], qb[0];
h qb[5];
x qb[5];
h qb[6];
h qb[7];
h qb[8];
h qb[9];
h qb[10];
x qb[6];
x qb[7];
x qb[8];
x qb[9];
x qb[10];
ccx qb[6], qb[7], qb[0];
ccx qb[0], qb[8], qb[1];
ccx qb[1], qb[9], qb[2];
cz qb[2], qb[10];
ccx qb[1], qb[9], qb[2];
ccx qb[0], qb[8], qb[1];
ccx qb[6], qb[7], qb[0];
x qb[6];
x qb[7];
x qb[8];
x qb[9];
x qb[10];
h qb[6];
h qb[7];
h qb[8];
h qb[9];
h qb[10];
ccx qb[6], qb[7], qb[0];
ccx qb[0], qb[8], qb[1];
ccx qb[1], qb[9], qb[2];
ccx qb[2], qb[10], qb[3];
cx qb[3], qb[5];
ccx qb[2], qb[10], qb[3];
ccx qb[1], qb[9], qb[2];
ccx qb[0], qb[8], qb[1];
ccx qb[6], qb[7], qb[0];
ck qb[5], qb[4];
ccx qb[6], qb[7], qb[0];
ccx qb[0], qb[8], qb[1];
ccx qb[1], qb[9], qb[2];
ccx qb[2], qb[10], qb[3];
cx qb[3], qb[5];
ccx qb[2], qb[10], qb[3];
ccx qb[1], qb[9], qb[2];
ccx qb[0], qb[8], qb[1];
ccx qb[6], qb[7], qb[0];
outcome[4] = measure qb[4];
}

// outcome = measure qb;
