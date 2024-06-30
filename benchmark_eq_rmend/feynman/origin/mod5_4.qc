.v 0 1 2 3 4
BEGIN
h qubits[4];
h qubits[4];
ccx qubits[0],qubits[3],qubits[4];
h qubits[4];
h qubits[4];
ccx qubits[2],qubits[3],qubits[4];
h qubits[4];
h qubits[4];
cx qubits[3],qubits[4];
h qubits[4];
h qubits[4];
ccx qubits[1],qubits[2],qubits[4];
h qubits[4];
h qubits[4];
cx qubits[2],qubits[4];
h qubits[4];
h qubits[4];
ccx qubits[0],qubits[1],qubits[4];
h qubits[4];
h qubits[4];
END
