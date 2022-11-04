# Feynman -- quantum circuit toolkit
# Original (./27/circuit.qc):
#   Qubits: 28
#   H: 56
#   Z: 1
#   cnot: 14
#   Depth: 17
#   T depth: 0
# Result (1.622ms):
#   Qubits: 28
#   H: 56
#   Z: 1
#   cnot: 14
#   Depth: 17
#   T depth: 0
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27
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
H q23
H q24
H q25
H q26
H q27
Z q27
tof q0 q27
tof q2 q27
tof q4 q27
tof q6 q27
tof q8 q27
tof q10 q27
tof q12 q27
tof q14 q27
tof q16 q27
tof q18 q27
tof q20 q27
tof q22 q27
tof q24 q27
tof q26 q27
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
H q23
H q24
H q25
H q26
H q27
END
