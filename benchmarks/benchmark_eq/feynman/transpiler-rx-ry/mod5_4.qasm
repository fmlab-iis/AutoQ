// Transpiled with:
//   Basis gates = ['x', 'y', 'z', 'h', 's', 't', 'cx', 'cz', 'ccx']
//   Optimization level = 3
// Result:
//   Circuit size: 23 -> 9
//   Circuit depth: 23 -> 9
OPENQASM 2.0;
include "qelib1.inc";
qreg q[5];
x q[4];
ccx q[0],q[3],q[4];
ccx q[2],q[3],q[4];
cx q[3],q[4];
ccx q[1],q[2],q[4];
cx q[2],q[4];
ccx q[0],q[1],q[4];
cx q[1],q[4];
cx q[0],q[4];
