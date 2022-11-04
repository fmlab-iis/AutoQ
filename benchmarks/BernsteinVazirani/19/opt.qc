# Feynman -- quantum circuit toolkit
# Original (./19/circuit.qc):
#   Qubits: 20
#   H: 40
#   Z: 1
#   cnot: 10
#   Depth: 13
#   T depth: 0
# Result (1.012ms):
#   Qubits: 20
#   H: 40
#   Z: 1
#   cnot: 10
#   Depth: 13
#   T depth: 0
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
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
Z q19
tof q0 q19
tof q2 q19
tof q4 q19
tof q6 q19
tof q8 q19
tof q10 q19
tof q12 q19
tof q14 q19
tof q16 q19
tof q18 q19
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
END
