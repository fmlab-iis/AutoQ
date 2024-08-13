OPENQASM 2.0;
include "qelib1.inc";
qreg q[4];
ccx q[1],q[0],q[3];
