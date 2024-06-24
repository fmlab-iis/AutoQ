OPENQASM 2.0;
include "qelib1.inc";
qreg q[4];
ccx q[1],q[0],q[3];
cx q[0],q[1];
ccx q[2],q[1],q[3];
cx q[1],q[2];
x q[3];
