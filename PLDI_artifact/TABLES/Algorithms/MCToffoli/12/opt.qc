# Feynman -- quantum circuit toolkit

#   Qubits: 24
#   H: 44
#   T: 154
#   cnot: 133
#   Depth: 167
#   T depth: 68
# Result (0.953ms):
#   Qubits: 24
#   H: 44
#   T: 154
#   cnot: 133
#   Depth: 167
#   T depth: 68
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23
BEGIN 
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q11 q10 q12
tof q13 q12 q14
tof q15 q14 q16
tof q17 q16 q18
tof q19 q18 q20
tof q21 q20 q22
tof q22 q23
tof q21 q20 q22
tof q19 q18 q20
tof q17 q16 q18
tof q15 q14 q16
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
END
