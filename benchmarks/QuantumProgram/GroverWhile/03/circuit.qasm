OPENQASM 3;
include "stdgates.inc";
qubit[7] qb;
bit[7] outcome;

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

h qb[4];
h qb[5];
h qb[6];
ccx qb[4], qb[5], qb[0];
ccx qb[0], qb[6], qb[1];
cx qb[1], qb[3];
ccx qb[0], qb[6], qb[1];
ccx qb[4], qb[5], qb[0];
ck qb[3], qb[2];
ccx qb[4], qb[5], qb[0];
ccx qb[0], qb[6], qb[1];
cx qb[1], qb[3];
ccx qb[0], qb[6], qb[1];
ccx qb[4], qb[5], qb[0];

outcome[2] = measure qb[2];
while (!outcome[2]) { // loop-invariant.lsta
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
ck qb[3], qb[2];
ccx qb[4], qb[5], qb[0];
ccx qb[0], qb[6], qb[1];
cx qb[1], qb[3];
ccx qb[0], qb[6], qb[1];
ccx qb[4], qb[5], qb[0];
outcome[2] = measure qb[2];
}

// outcome = measure qb;
