// Transpiled with:
//   Basis gates = ['x', 'y', 'z', 's', 't', 'cx', 'cz', 'ccx']
//   Optimization level = 3
// Result:
//   Circuit size: 15 -> 3
//   Circuit depth: 11 -> 3
OPENQASM 2.0;
include "qelib1.inc";
qreg q[5];
ccx q[0],q[1],q[4];
ccx q[2],q[4],q[3];
ccx q[0],q[1],q[4];
