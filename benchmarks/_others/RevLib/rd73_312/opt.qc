# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/rd73_312/circuit.qc):
#   Qubits: 25
#   H: 72
#   T: 252
#   X: 7
#   cnot: 246
#   Depth: 188
#   T depth: 83
# Result (2.193ms):
#   Qubits: 25
#   H: 72
#   T: 252
#   X: 7
#   cnot: 246
#   Depth: 188
#   T depth: 83
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24
BEGIN 
tof q5 q7
tof q5 q6 q7
tof q6 q7
tof q5 q6 q8
tof q8 q9
tof q0 q7 q9
tof q0 q8 q9
tof q0 q10
tof q7 q10
tof q0 q8 q10
tof q0 q7 q10
tof q10 q11
tof q4 q9 q11
tof q4 q10 q11
tof q4 q12
tof q9 q12
tof q4 q10 q12
tof q4 q9 q12
tof q12 q13
tof q1 q11 q13
tof q1 q12 q13
tof q11
tof q1 q11 q12
tof q1 q12 q11
tof q11 q14
tof q2 q13 q14
tof q2 q11 q14
tof q13
tof q2 q13 q11
tof q2 q11 q13
tof q13 q14
tof q3 q14 q13
tof q5 q15
tof q6 q15
tof q0 q15
tof q15
tof q4 q15
tof q15
tof q1 q15
tof q15
tof q2 q15
tof q15
tof q3 q15
tof q15
tof q0 q16
tof q0 q7 q16
tof q7 q16
tof q4 q17
tof q4 q16 q17
tof q16 q17
tof q9 q18
tof q4 q16 q18
tof q4 q9 q18
tof q18 q19
tof q1 q17 q19
tof q1 q18 q19
tof q0 q8 q20
tof q20 q21
tof q4 q9 q21
tof q4 q20 q21
tof q21 q22
tof q1 q18 q22
tof q1 q21 q22
tof q22 q23
tof q2 q19 q23
tof q2 q22 q23
tof q4 q20 q24
tof q24 q21
tof q1 q21 q24
tof q24 q22
tof q2 q22 q24
tof q24 q23
tof q3 q23 q24
END
