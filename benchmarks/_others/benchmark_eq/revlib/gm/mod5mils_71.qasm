OPENQASM 2.0;
include "qelib1.inc";
qreg q[5];
x q[3];
ccx q[2],q[3],q[4];
ccx q[0],q[3],q[4];
cx q[3],q[4];
