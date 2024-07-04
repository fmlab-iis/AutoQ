// Transpiled with:
//   Basis gates = ['x', 'y', 'z', 'h', 's', 't', 'cx', 'cz', 'ccx']
//   Optimization level = 3
// Result:
//   Circuit size: 20 -> 4
//   Circuit depth: 14 -> 4
OPENQASM 2.0;
include "qelib1.inc";
qreg q[5];
ccx q[2],q[3],q[4];
ccx q[0],q[1],q[3];
ccx q[2],q[3],q[4];
ccx q[0],q[1],q[3];
