OPENQASM 2.0;
include "qelib1.inc";
qreg q[5];
x q[3];
cx q[1],q[3];
cx q[3],q[4];
ccx q[3],q[2],q[4];
ccx q[3],q[0],q[4];
