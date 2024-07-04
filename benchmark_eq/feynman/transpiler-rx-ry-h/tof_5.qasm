// Transpiled with:
//   Basis gates = ['x', 'y', 'z', 's', 't', 'cx', 'cz', 'ccx']
//   Optimization level = 3
// Result:
//   Circuit size: 35 -> 7
//   Circuit depth: 23 -> 7
OPENQASM 2.0;
include "qelib1.inc";
qreg q[9];
ccx q[0],q[1],q[5];
ccx q[2],q[5],q[6];
ccx q[3],q[6],q[7];
ccx q[4],q[7],q[8];
ccx q[3],q[6],q[7];
ccx q[2],q[5],q[6];
ccx q[0],q[1],q[5];
