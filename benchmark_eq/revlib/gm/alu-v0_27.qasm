OPENQASM 2.0;
include "qelib1.inc";
qreg q[5];
cx q[2],q[1];
cx q[3],q[4];
ccx q[3],q[1],q[2];
x q[2];
ccx q[4],q[0],q[2];
