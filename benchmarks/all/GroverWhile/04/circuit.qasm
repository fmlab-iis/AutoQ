OPENQASM 3;
include "stdgates.inc";
qubit[9] qb;
bit[9] outcome;

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

h qb[5];
h qb[6];
h qb[7];
h qb[8];
ccx qb[5], qb[6], qb[0];
ccx qb[0], qb[7], qb[1];
ccx qb[1], qb[8], qb[2];
cx qb[2], qb[4];
ccx qb[1], qb[8], qb[2];
ccx qb[0], qb[7], qb[1];
ccx qb[5], qb[6], qb[0];
ck qb[4], qb[3];
ccx qb[5], qb[6], qb[0];
ccx qb[0], qb[7], qb[1];
ccx qb[1], qb[8], qb[2];
cx qb[2], qb[4];
ccx qb[1], qb[8], qb[2];
ccx qb[0], qb[7], qb[1];
ccx qb[5], qb[6], qb[0];

outcome[3] = measure qb[3];
while (!outcome[3]) { // loop-invariant.hsl
x qb[4];
h qb[4];
ccx qb[5], qb[6], qb[0];
ccx qb[0], qb[7], qb[1];
ccx qb[1], qb[8], qb[2];
cx qb[2], qb[4];
ccx qb[1], qb[8], qb[2];
ccx qb[0], qb[7], qb[1];
ccx qb[5], qb[6], qb[0];
h qb[4];
x qb[4];
h qb[5];
h qb[6];
h qb[7];
h qb[8];
x qb[5];
x qb[6];
x qb[7];
x qb[8];
ccx qb[5], qb[6], qb[0];
ccx qb[0], qb[7], qb[1];
cz qb[1], qb[8];
ccx qb[0], qb[7], qb[1];
ccx qb[5], qb[6], qb[0];
x qb[5];
x qb[6];
x qb[7];
x qb[8];
h qb[5];
h qb[6];
h qb[7];
h qb[8];
ccx qb[5], qb[6], qb[0];
ccx qb[0], qb[7], qb[1];
ccx qb[1], qb[8], qb[2];
cx qb[2], qb[4];
ccx qb[1], qb[8], qb[2];
ccx qb[0], qb[7], qb[1];
ccx qb[5], qb[6], qb[0];
ck qb[4], qb[3];
ccx qb[5], qb[6], qb[0];
ccx qb[0], qb[7], qb[1];
ccx qb[1], qb[8], qb[2];
cx qb[2], qb[4];
ccx qb[1], qb[8], qb[2];
ccx qb[0], qb[7], qb[1];
ccx qb[5], qb[6], qb[0];
outcome[3] = measure qb[3];
}

// outcome = measure qb;
