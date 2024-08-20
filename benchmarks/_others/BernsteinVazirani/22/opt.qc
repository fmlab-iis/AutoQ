# Feynman -- quantum circuit toolkit
# Original (./22/circuit.qc):
#   Qubits: 23
#   H: 46
#   Z: 1
#   cnot: 11
#   Depth: 14
#   T depth: 0
# Result (1.030ms):
#   Qubits: 23
#   H: 46
#   Z: 1
#   cnot: 11
#   Depth: 14
#   T depth: 0
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22
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
H q16
H q17
H q18
H q19
H q20
H q21
H q22
Z q22
tof q0 q22
tof q2 q22
tof q4 q22
tof q6 q22
tof q8 q22
tof q10 q22
tof q12 q22
tof q14 q22
tof q16 q22
tof q18 q22
tof q20 q22
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
H q16
H q17
H q18
H q19
H q20
H q21
H q22
END
