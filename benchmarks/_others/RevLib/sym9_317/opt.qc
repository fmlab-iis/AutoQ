# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/sym9_317/circuit.qc):
#   Qubits: 27
#   H: 72
#   T: 252
#   X: 2
#   cnot: 240
#   Depth: 206
#   T depth: 89
# Result (2.173ms):
#   Qubits: 27
#   H: 72
#   T: 252
#   X: 2
#   cnot: 240
#   Depth: 206
#   T depth: 89
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26
BEGIN 
tof q0 q9
tof q0 q8 q9
tof q8 q9
tof q7 q10
tof q7 q9 q10
tof q9 q10
tof q0 q8 q11
tof q11 q12
tof q7 q9 q12
tof q7 q11 q12
tof q12 q13
tof q1 q10 q13
tof q1 q12 q13
tof q7 q11 q14
tof q14 q15
tof q1 q12 q15
tof q1 q14 q15
tof q15 q16
tof q6 q13 q16
tof q6 q15 q16
tof q1 q14 q17
tof q17 q18
tof q6 q15 q18
tof q6 q17 q18
tof q18 q19
tof q2 q16 q19
tof q2 q18 q19
tof q1 q20
tof q1 q10 q20
tof q10 q20
tof q6 q21
tof q20 q21
tof q6 q17 q21
tof q6 q20 q21
tof q21 q22
tof q2 q18 q22
tof q2 q21 q22
tof q22 q23
tof q5 q19 q23
tof q5 q22 q23
tof q13 q20
tof q6 q20 q13
tof q2 q24
tof q13 q24
tof q2 q21 q24
tof q2 q13 q24
tof q24 q25
tof q5 q22 q25
tof q5 q24 q25
tof q25 q26
tof q4 q23 q26
tof q4 q25 q26
tof q16 q13
tof q2 q13 q16
tof q16
tof q5 q16 q24
tof q5 q24 q16
tof q16 q25
tof q4 q25 q16
tof q16 q26
tof q3 q26 q16
tof q16
END
