// Transpiled with:
//   Basis gates = ['x', 'y', 'z', 's', 't', 'cx', 'cz', 'ccx']
//   Optimization level = 3
// Result:
//   Circuit size: 90 -> 46
//   Circuit depth: 40 -> 16
OPENQASM 2.0;
include "qelib1.inc";
qreg q[14];
cx q[4],q[3];
cx q[4],q[2];
ccx q[0],q[1],q[2];
cx q[6],q[5];
cx q[6],q[4];
ccx q[2],q[3],q[4];
x q[3];
cx q[2],q[3];
cx q[8],q[7];
cx q[8],q[6];
ccx q[4],q[5],q[6];
x q[5];
cx q[4],q[5];
cx q[10],q[9];
cx q[10],q[8];
ccx q[6],q[7],q[8];
x q[7];
cx q[6],q[7];
cx q[12],q[11];
cx q[12],q[10];
ccx q[8],q[9],q[10];
x q[9];
cx q[8],q[9];
cx q[12],q[13];
ccx q[10],q[11],q[13];
cx q[10],q[11];
ccx q[8],q[9],q[10];
ccx q[6],q[7],q[8];
ccx q[4],q[5],q[6];
ccx q[2],q[3],q[4];
ccx q[0],q[1],q[2];
cx q[1],q[0];
x q[3];
x q[5];
x q[7];
x q[9];
cx q[12],q[10];
cx q[10],q[8];
cx q[8],q[6];
cx q[6],q[4];
cx q[4],q[2];
cx q[4],q[3];
cx q[6],q[5];
cx q[8],q[7];
cx q[10],q[9];
cx q[12],q[11];
