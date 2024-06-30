.v 0 1 2 3 4 5 6
BEGIN
h qubits[6];
h qubits[6];
ccx qubits[3],qubits[5],qubits[6];
h qubits[6];
h qubits[5];
h qubits[5];
ccx qubits[2],qubits[4],qubits[5];
h qubits[5];
h qubits[4];
h qubits[4];
ccx qubits[0],qubits[1],qubits[4];
h qubits[4];
h qubits[4];
h qubits[5];
ccx qubits[2],qubits[4],qubits[5];
h qubits[5];
h qubits[5];
h qubits[6];
ccx qubits[3],qubits[5],qubits[6];
h qubits[6];
h qubits[6];
h qubits[5];
h qubits[5];
ccx qubits[2],qubits[4],qubits[5];
h qubits[5];
h qubits[4];
h qubits[4];
ccx qubits[0],qubits[1],qubits[4];
h qubits[4];
h qubits[4];
h qubits[5];
ccx qubits[2],qubits[4],qubits[5];
h qubits[5];
h qubits[5];
END
