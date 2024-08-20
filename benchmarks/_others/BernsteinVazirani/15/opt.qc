# Feynman -- quantum circuit toolkit
# Original (./15/circuit.qc):
#   Qubits: 16
#   H: 32
#   Z: 1
#   cnot: 8
#   Depth: 11
#   T depth: 0
# Result (0.937ms):
#   Qubits: 16
#   H: 32
#   Z: 1
#   cnot: 8
#   Depth: 11
#   T depth: 0
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
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
H q13
H q14
H q15
Z q15
tof q0 q15
tof q2 q15
tof q4 q15
tof q6 q15
tof q8 q15
tof q10 q15
tof q12 q15
tof q14 q15
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
H q13
H q14
H q15
END
