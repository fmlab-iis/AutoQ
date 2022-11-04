# Feynman -- quantum circuit toolkit
# Original (./12/circuit.qc):
#   Qubits: 13
#   H: 26
#   Z: 1
#   cnot: 6
#   Depth: 9
#   T depth: 0
# Result (0.856ms):
#   Qubits: 13
#   H: 26
#   Z: 1
#   cnot: 6
#   Depth: 9
#   T depth: 0
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
BEGIN 
H q0
H q1
H q2
H q3
H q4
H q5
H q6
H q7
H q8
H q9
H q10
H q11
H q12
Z q12
tof q0 q12
tof q2 q12
tof q4 q12
tof q6 q12
tof q8 q12
tof q10 q12
H q0
H q1
H q2
H q3
H q4
H q5
H q6
H q7
H q8
H q9
H q10
H q11
H q12
END
