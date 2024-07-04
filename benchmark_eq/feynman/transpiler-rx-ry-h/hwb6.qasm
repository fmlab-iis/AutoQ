// Transpiled with:
//   Basis gates = ['x', 'y', 'z', 's', 't', 'cx', 'cz', 'ccx']
//   Optimization level = 3
// Result:
//   Circuit size: 109 -> 47
//   Circuit depth: 62 -> 34
OPENQASM 2.0;
include "qelib1.inc";
qreg q[7];
x q[0];
cx q[2],q[0];
ccx q[0],q[1],q[2];
ccx q[0],q[2],q[1];
cx q[5],q[3];
cx q[1],q[3];
x q[1];
cx q[4],q[5];
ccx q[0],q[2],q[5];
ccx q[1],q[3],q[5];
cx q[0],q[1];
cx q[1],q[0];
cx q[5],q[4];
cx q[0],q[4];
cx q[0],q[1];
ccx q[1],q[2],q[3];
cx q[1],q[5];
x q[5];
ccx q[4],q[5],q[2];
ccx q[2],q[4],q[6];
ccx q[6],q[5],q[1];
ccx q[2],q[4],q[6];
cx q[5],q[0];
cx q[0],q[3];
cx q[3],q[4];
cx q[4],q[0];
cx q[5],q[2];
ccx q[1],q[2],q[5];
ccx q[2],q[4],q[5];
cx q[3],q[1];
cx q[5],q[2];
cx q[4],q[5];
ccx q[1],q[4],q[3];
ccx q[0],q[3],q[5];
x q[0];
cx q[0],q[2];
ccx q[1],q[4],q[0];
cx q[3],q[2];
ccx q[0],q[2],q[1];
cx q[1],q[0];
cx q[2],q[4];
x q[2];
cx q[1],q[2];
cx q[0],q[1];
cx q[3],q[4];
cx q[5],q[3];
x q[5];
