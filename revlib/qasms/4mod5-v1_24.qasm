OPENQASM 2.0;
include "qelib1.inc";
qreg q[5];
cx q[3],q[1];
ccx q[4],q[2],q[0];
cx q[1],q[4];
x q[1];
ccx q[1],q[0],q[4];
