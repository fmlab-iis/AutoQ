OPENQASM 2.0;
include "qelib1.inc";
qreg q[4];
ccx q[2],q[0],q[3];
ccx q[0],q[2],q[1];
x q[0];
cx q[3],q[2];
x q[3];
