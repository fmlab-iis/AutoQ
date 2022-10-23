# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/MOGrover/7/circuit.qc):
#   Qubits: 21
#   H: 472
#   T: 1232
#   X: 113
#   cnot: 1176
#   cz: 8
#   Depth: 1401
#   T depth: 560
# Result (6.938ms):
#   Qubits: 21
#   H: 472
#   T: 1232
#   X: 113
#   cnot: 1176
#   cz: 8
#   Depth: 1401
#   T depth: 560
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
BEGIN 
tof q20
H q7
H q8
H q10
H q12
H q14
H q16
H q18
H q20
tof q0 q7
tof q1 q8
tof q2 q10
tof q3 q12
tof q4 q14
tof q5 q16
tof q6 q18
tof q7 q8 q9
tof q10 q9 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q19 q20
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q10 q9 q11
tof q7 q8 q9
tof q0 q7
tof q1 q8
tof q2 q10
tof q3 q12
tof q4 q14
tof q5 q16
tof q6 q18
H q7
H q8
H q10
H q12
H q14
H q16
H q18
tof q7
tof q8
tof q10
tof q12
tof q14
tof q16
tof q18
tof q7 q8 q9
tof q10 q9 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
Z q17 q18
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q10 q9 q11
tof q7 q8 q9
tof q7
tof q8
tof q10
tof q12
tof q14
tof q16
tof q18
H q7
H q8
H q10
H q12
H q14
H q16
H q18
tof q0 q7
tof q1 q8
tof q2 q10
tof q3 q12
tof q4 q14
tof q5 q16
tof q6 q18
tof q7 q8 q9
tof q10 q9 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q19 q20
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q10 q9 q11
tof q7 q8 q9
tof q0 q7
tof q1 q8
tof q2 q10
tof q3 q12
tof q4 q14
tof q5 q16
tof q6 q18
H q7
H q8
H q10
H q12
H q14
H q16
H q18
tof q7
tof q8
tof q10
tof q12
tof q14
tof q16
tof q18
tof q7 q8 q9
tof q10 q9 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
Z q17 q18
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q10 q9 q11
tof q7 q8 q9
tof q7
tof q8
tof q10
tof q12
tof q14
tof q16
tof q18
H q7
H q8
H q10
H q12
H q14
H q16
H q18
tof q0 q7
tof q1 q8
tof q2 q10
tof q3 q12
tof q4 q14
tof q5 q16
tof q6 q18
tof q7 q8 q9
tof q10 q9 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q19 q20
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q10 q9 q11
tof q7 q8 q9
tof q0 q7
tof q1 q8
tof q2 q10
tof q3 q12
tof q4 q14
tof q5 q16
tof q6 q18
H q7
H q8
H q10
H q12
H q14
H q16
H q18
tof q7
tof q8
tof q10
tof q12
tof q14
tof q16
tof q18
tof q7 q8 q9
tof q10 q9 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
Z q17 q18
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q10 q9 q11
tof q7 q8 q9
tof q7
tof q8
tof q10
tof q12
tof q14
tof q16
tof q18
H q7
H q8
H q10
H q12
H q14
H q16
H q18
tof q0 q7
tof q1 q8
tof q2 q10
tof q3 q12
tof q4 q14
tof q5 q16
tof q6 q18
tof q7 q8 q9
tof q10 q9 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q19 q20
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q10 q9 q11
tof q7 q8 q9
tof q0 q7
tof q1 q8
tof q2 q10
tof q3 q12
tof q4 q14
tof q5 q16
tof q6 q18
H q7
H q8
H q10
H q12
H q14
H q16
H q18
tof q7
tof q8
tof q10
tof q12
tof q14
tof q16
tof q18
tof q7 q8 q9
tof q10 q9 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
Z q17 q18
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q10 q9 q11
tof q7 q8 q9
tof q7
tof q8
tof q10
tof q12
tof q14
tof q16
tof q18
H q7
H q8
H q10
H q12
H q14
H q16
H q18
tof q0 q7
tof q1 q8
tof q2 q10
tof q3 q12
tof q4 q14
tof q5 q16
tof q6 q18
tof q7 q8 q9
tof q10 q9 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q19 q20
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q10 q9 q11
tof q7 q8 q9
tof q0 q7
tof q1 q8
tof q2 q10
tof q3 q12
tof q4 q14
tof q5 q16
tof q6 q18
H q7
H q8
H q10
H q12
H q14
H q16
H q18
tof q7
tof q8
tof q10
tof q12
tof q14
tof q16
tof q18
tof q7 q8 q9
tof q10 q9 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
Z q17 q18
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q10 q9 q11
tof q7 q8 q9
tof q7
tof q8
tof q10
tof q12
tof q14
tof q16
tof q18
H q7
H q8
H q10
H q12
H q14
H q16
H q18
tof q0 q7
tof q1 q8
tof q2 q10
tof q3 q12
tof q4 q14
tof q5 q16
tof q6 q18
tof q7 q8 q9
tof q10 q9 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q19 q20
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q10 q9 q11
tof q7 q8 q9
tof q0 q7
tof q1 q8
tof q2 q10
tof q3 q12
tof q4 q14
tof q5 q16
tof q6 q18
H q7
H q8
H q10
H q12
H q14
H q16
H q18
tof q7
tof q8
tof q10
tof q12
tof q14
tof q16
tof q18
tof q7 q8 q9
tof q10 q9 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
Z q17 q18
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q10 q9 q11
tof q7 q8 q9
tof q7
tof q8
tof q10
tof q12
tof q14
tof q16
tof q18
H q7
H q8
H q10
H q12
H q14
H q16
H q18
tof q0 q7
tof q1 q8
tof q2 q10
tof q3 q12
tof q4 q14
tof q5 q16
tof q6 q18
tof q7 q8 q9
tof q10 q9 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q19 q20
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q10 q9 q11
tof q7 q8 q9
tof q0 q7
tof q1 q8
tof q2 q10
tof q3 q12
tof q4 q14
tof q5 q16
tof q6 q18
H q7
H q8
H q10
H q12
H q14
H q16
H q18
tof q7
tof q8
tof q10
tof q12
tof q14
tof q16
tof q18
tof q7 q8 q9
tof q10 q9 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
Z q17 q18
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q10 q9 q11
tof q7 q8 q9
tof q7
tof q8
tof q10
tof q12
tof q14
tof q16
tof q18
H q7
H q8
H q10
H q12
H q14
H q16
H q18
tof q0 q7
tof q1 q8
tof q2 q10
tof q3 q12
tof q4 q14
tof q5 q16
tof q6 q18
tof q7 q8 q9
tof q10 q9 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q19 q20
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q10 q9 q11
tof q7 q8 q9
tof q0 q7
tof q1 q8
tof q2 q10
tof q3 q12
tof q4 q14
tof q5 q16
tof q6 q18
H q7
H q8
H q10
H q12
H q14
H q16
H q18
tof q7
tof q8
tof q10
tof q12
tof q14
tof q16
tof q18
tof q7 q8 q9
tof q10 q9 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
Z q17 q18
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q10 q9 q11
tof q7 q8 q9
tof q7
tof q8
tof q10
tof q12
tof q14
tof q16
tof q18
H q7
H q8
H q10
H q12
H q14
H q16
H q18
END
