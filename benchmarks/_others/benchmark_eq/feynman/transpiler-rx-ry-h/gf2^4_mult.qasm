// Transpiled with:
//   Basis gates = ['x', 'y', 'z', 's', 't', 'cx', 'cz', 'ccx']
//   Optimization level = 3
// Result:
//   Circuit size: 65 -> 19
//   Circuit depth: 31 -> 13
OPENQASM 2.0;
include "qelib1.inc";
qreg q[12];
ccx q[3],q[5],q[8];
ccx q[2],q[6],q[8];
ccx q[1],q[7],q[8];
ccx q[3],q[6],q[9];
ccx q[2],q[7],q[9];
ccx q[3],q[7],q[10];
cx q[10],q[11];
ccx q[3],q[4],q[11];
ccx q[2],q[5],q[11];
ccx q[1],q[6],q[11];
ccx q[0],q[7],q[11];
cx q[9],q[10];
ccx q[2],q[4],q[10];
ccx q[1],q[5],q[10];
ccx q[0],q[6],q[10];
cx q[8],q[9];
ccx q[1],q[4],q[9];
ccx q[0],q[5],q[9];
ccx q[0],q[4],q[8];
