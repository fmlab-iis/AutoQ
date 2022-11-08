// Feynman -- quantum circuit toolkit
// Original (./BernsteinVazirani/20/circuit.qasm):
//   cbits: 0
//   qubits: 21
//   H: 42
//   Z: 1
//   cnot: 10
// Result (1.000ms):
//   cbits: 0
//   qubits: 21
//   H: 42
//   Z: 1
//   cnot: 10
OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[21];
h qubits[0];
h qubits[1];
h qubits[2];
h qubits[3];
h qubits[4];
h qubits[5];
h qubits[6];
h qubits[7];
h qubits[8];
h qubits[9];
h qubits[10];
h qubits[11];
h qubits[12];
h qubits[13];
h qubits[14];
h qubits[15];
h qubits[16];
h qubits[17];
h qubits[18];
h qubits[19];
h qubits[20];
z qubits[20];
cx qubits[0],qubits[20];
cx qubits[2],qubits[20];
cx qubits[4],qubits[20];
cx qubits[6],qubits[20];
cx qubits[8],qubits[20];
cx qubits[10],qubits[20];
cx qubits[12],qubits[20];
cx qubits[14],qubits[20];
cx qubits[16],qubits[20];
cx qubits[18],qubits[20];
h qubits[0];
h qubits[1];
h qubits[2];
h qubits[3];
h qubits[4];
h qubits[5];
h qubits[6];
h qubits[7];
h qubits[8];
h qubits[9];
h qubits[10];
h qubits[11];
h qubits[12];
h qubits[13];
h qubits[14];
h qubits[15];
h qubits[16];
h qubits[17];
h qubits[18];
h qubits[19];
h qubits[20];
