OPENQASM 2.0;
include "qelib1.inc";
qreg qubits[2];

for int i in [1:5] {
    t qubits[0];
    cx qubits[0], qubits[1];
}