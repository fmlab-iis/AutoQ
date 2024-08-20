OPENQASM 2.0;
include "qelib1.inc";
qreg q[3];
cx q[0],q[1];
ccx q[1],q[2],q[0];
cx q[0],q[1];
x q[0];
