// Transpiled with:
//   Basis gates = ['x', 'y', 'z', 's', 't', 'cx', 'cz', 'ccx']
//   Optimization level = 3
// Result:
//   Circuit size: 97 -> 29
//   Circuit depth: 38 -> 16
OPENQASM 2.0;
include "qelib1.inc";
qreg q[15];
ccx q[4],q[6],q[10];
ccx q[3],q[7],q[10];
ccx q[2],q[8],q[10];
ccx q[1],q[9],q[10];
ccx q[4],q[7],q[11];
ccx q[3],q[8],q[11];
ccx q[2],q[9],q[11];
ccx q[4],q[8],q[12];
ccx q[3],q[9],q[12];
ccx q[4],q[9],q[13];
cx q[13],q[10];
cx q[11],q[13];
cx q[12],q[14];
ccx q[4],q[5],q[14];
ccx q[3],q[6],q[14];
ccx q[2],q[7],q[14];
ccx q[1],q[8],q[14];
ccx q[0],q[9],q[14];
ccx q[3],q[5],q[13];
ccx q[2],q[6],q[13];
ccx q[1],q[7],q[13];
ccx q[0],q[8],q[13];
cx q[10],q[12];
ccx q[2],q[5],q[12];
ccx q[1],q[6],q[12];
ccx q[0],q[7],q[12];
ccx q[1],q[5],q[11];
ccx q[0],q[6],q[11];
ccx q[0],q[5],q[10];
