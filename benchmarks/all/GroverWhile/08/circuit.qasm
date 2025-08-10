OPENQASM 3;
include "stdgates.inc";
qubit[17] qb;
bit[17] outcome;

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

h qb[9];
h qb[10];
h qb[11];
h qb[12];
h qb[13];
h qb[14];
h qb[15];
h qb[16];
ccx qb[9], qb[10], qb[0];
ccx qb[0], qb[11], qb[1];
ccx qb[1], qb[12], qb[2];
ccx qb[2], qb[13], qb[3];
ccx qb[3], qb[14], qb[4];
ccx qb[4], qb[15], qb[5];
ccx qb[5], qb[16], qb[6];
cx qb[6], qb[8];
ccx qb[5], qb[16], qb[6];
ccx qb[4], qb[15], qb[5];
ccx qb[3], qb[14], qb[4];
ccx qb[2], qb[13], qb[3];
ccx qb[1], qb[12], qb[2];
ccx qb[0], qb[11], qb[1];
ccx qb[9], qb[10], qb[0];
ck qb[8], qb[7];
ccx qb[9], qb[10], qb[0];
ccx qb[0], qb[11], qb[1];
ccx qb[1], qb[12], qb[2];
ccx qb[2], qb[13], qb[3];
ccx qb[3], qb[14], qb[4];
ccx qb[4], qb[15], qb[5];
ccx qb[5], qb[16], qb[6];
cx qb[6], qb[8];
ccx qb[5], qb[16], qb[6];
ccx qb[4], qb[15], qb[5];
ccx qb[3], qb[14], qb[4];
ccx qb[2], qb[13], qb[3];
ccx qb[1], qb[12], qb[2];
ccx qb[0], qb[11], qb[1];
ccx qb[9], qb[10], qb[0];

outcome[7] = measure qb[7];
while (!outcome[7]) { // loop-invariant.hsl
x qb[8];
h qb[8];
ccx qb[9], qb[10], qb[0];
ccx qb[0], qb[11], qb[1];
ccx qb[1], qb[12], qb[2];
ccx qb[2], qb[13], qb[3];
ccx qb[3], qb[14], qb[4];
ccx qb[4], qb[15], qb[5];
ccx qb[5], qb[16], qb[6];
cx qb[6], qb[8];
ccx qb[5], qb[16], qb[6];
ccx qb[4], qb[15], qb[5];
ccx qb[3], qb[14], qb[4];
ccx qb[2], qb[13], qb[3];
ccx qb[1], qb[12], qb[2];
ccx qb[0], qb[11], qb[1];
ccx qb[9], qb[10], qb[0];
h qb[8];
x qb[8];
h qb[9];
h qb[10];
h qb[11];
h qb[12];
h qb[13];
h qb[14];
h qb[15];
h qb[16];
x qb[9];
x qb[10];
x qb[11];
x qb[12];
x qb[13];
x qb[14];
x qb[15];
x qb[16];
ccx qb[9], qb[10], qb[0];
ccx qb[0], qb[11], qb[1];
ccx qb[1], qb[12], qb[2];
ccx qb[2], qb[13], qb[3];
ccx qb[3], qb[14], qb[4];
ccx qb[4], qb[15], qb[5];
cz qb[5], qb[16];
ccx qb[4], qb[15], qb[5];
ccx qb[3], qb[14], qb[4];
ccx qb[2], qb[13], qb[3];
ccx qb[1], qb[12], qb[2];
ccx qb[0], qb[11], qb[1];
ccx qb[9], qb[10], qb[0];
x qb[9];
x qb[10];
x qb[11];
x qb[12];
x qb[13];
x qb[14];
x qb[15];
x qb[16];
h qb[9];
h qb[10];
h qb[11];
h qb[12];
h qb[13];
h qb[14];
h qb[15];
h qb[16];
ccx qb[9], qb[10], qb[0];
ccx qb[0], qb[11], qb[1];
ccx qb[1], qb[12], qb[2];
ccx qb[2], qb[13], qb[3];
ccx qb[3], qb[14], qb[4];
ccx qb[4], qb[15], qb[5];
ccx qb[5], qb[16], qb[6];
cx qb[6], qb[8];
ccx qb[5], qb[16], qb[6];
ccx qb[4], qb[15], qb[5];
ccx qb[3], qb[14], qb[4];
ccx qb[2], qb[13], qb[3];
ccx qb[1], qb[12], qb[2];
ccx qb[0], qb[11], qb[1];
ccx qb[9], qb[10], qb[0];
ck qb[8], qb[7];
ccx qb[9], qb[10], qb[0];
ccx qb[0], qb[11], qb[1];
ccx qb[1], qb[12], qb[2];
ccx qb[2], qb[13], qb[3];
ccx qb[3], qb[14], qb[4];
ccx qb[4], qb[15], qb[5];
ccx qb[5], qb[16], qb[6];
cx qb[6], qb[8];
ccx qb[5], qb[16], qb[6];
ccx qb[4], qb[15], qb[5];
ccx qb[3], qb[14], qb[4];
ccx qb[2], qb[13], qb[3];
ccx qb[1], qb[12], qb[2];
ccx qb[0], qb[11], qb[1];
ccx qb[9], qb[10], qb[0];
outcome[7] = measure qb[7];
}

// outcome = measure qb;
