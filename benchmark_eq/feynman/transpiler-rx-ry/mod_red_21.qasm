// Transpiled with:
//   Basis gates = ['x', 'y', 'z', 'h', 's', 't', 'cx', 'cz', 'ccx']
//   Optimization level = 3
// Result:
//   Circuit size: 108 -> 30
//   Circuit depth: 58 -> 24
OPENQASM 2.0;
include "qelib1.inc";
qreg q[11];
ccx q[1],q[3],q[4];
x q[4];
x q[5];
ccx q[4],q[5],q[6];
x q[6];
ccx q[6],q[7],q[9];
ccx q[4],q[5],q[6];
ccx q[1],q[3],q[4];
x q[5];
ccx q[10],q[9],q[8];
cx q[8],q[0];
cx q[8],q[1];
ccx q[0],q[1],q[2];
x q[2];
ccx q[2],q[3],q[4];
cx q[8],q[5];
ccx q[4],q[5],q[6];
ccx q[6],q[8],q[7];
x q[6];
ccx q[4],q[5],q[6];
x q[4];
ccx q[4],q[8],q[5];
ccx q[2],q[3],q[4];
ccx q[2],q[8],q[3];
x q[2];
ccx q[0],q[1],q[2];
x q[0];
ccx q[0],q[8],q[1];
x q[0];
ccx q[10],q[9],q[8];
