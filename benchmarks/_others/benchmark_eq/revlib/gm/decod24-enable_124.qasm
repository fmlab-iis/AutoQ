OPENQASM 2.0;
include "qelib1.inc";
qreg q[6];
ccx q[1],q[4],q[2];
ccx q[1],q[5],q[3];
