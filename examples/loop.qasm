OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[8];

for int i in [1:4] {
    h qubits[0];
    h qubits[1];
    h qubits[3];
    h qubits[5];
    h qubits[7];
}