.v 0 1 2 3 4
BEGIN
h qubits[4];
h qubits[4];
ccx qubits[2],qubits[3],qubits[4];
h qubits[4];
h qubits[4];
h qubits[3];
h qubits[3];
ccx qubits[0],qubits[1],qubits[3];
h qubits[3];
h qubits[3];
h qubits[4];
h qubits[4];
ccx qubits[2],qubits[3],qubits[4];
h qubits[4];
h qubits[4];
h qubits[3];
h qubits[3];
ccx qubits[0],qubits[1],qubits[3];
h qubits[3];
h qubits[3];
END
