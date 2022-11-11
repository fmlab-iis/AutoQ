# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/MOGrover/09/circuit.qc):
#   Qubits: 27
#   H: 1337
#   T: 3570
#   X: 325
#   cnot: 3383
#   cz: 17
#   Depth: 3996
#   T depth: 1598
# Result (14.794ms):
#   Qubits: 27
#   H: 1337
#   T: 3570
#   X: 325
#   cnot: 3383
#   cz: 17
#   Depth: 3996
#   T depth: 1598
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26
BEGIN 
tof q26
tof q0
tof q1
tof q2
tof q3
tof q4
tof q5
tof q6
tof q7
tof q8
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
H q26
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
tof q24 q23 q25
tof q25 q26
tof q24 q23 q25
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
Z q23 q24
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
tof q24 q23 q25
tof q25 q26
tof q24 q23 q25
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
Z q23 q24
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
tof q24 q23 q25
tof q25 q26
tof q24 q23 q25
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
Z q23 q24
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
tof q24 q23 q25
tof q25 q26
tof q24 q23 q25
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
Z q23 q24
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
tof q24 q23 q25
tof q25 q26
tof q24 q23 q25
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
Z q23 q24
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
tof q24 q23 q25
tof q25 q26
tof q24 q23 q25
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
Z q23 q24
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
tof q24 q23 q25
tof q25 q26
tof q24 q23 q25
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
Z q23 q24
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
tof q24 q23 q25
tof q25 q26
tof q24 q23 q25
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
Z q23 q24
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
tof q24 q23 q25
tof q25 q26
tof q24 q23 q25
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
Z q23 q24
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
tof q24 q23 q25
tof q25 q26
tof q24 q23 q25
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
Z q23 q24
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
tof q24 q23 q25
tof q25 q26
tof q24 q23 q25
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
Z q23 q24
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
tof q24 q23 q25
tof q25 q26
tof q24 q23 q25
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
Z q23 q24
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
tof q24 q23 q25
tof q25 q26
tof q24 q23 q25
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
Z q23 q24
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
tof q24 q23 q25
tof q25 q26
tof q24 q23 q25
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
Z q23 q24
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
tof q24 q23 q25
tof q25 q26
tof q24 q23 q25
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
Z q23 q24
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
tof q24 q23 q25
tof q25 q26
tof q24 q23 q25
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
Z q23 q24
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
tof q24 q23 q25
tof q25 q26
tof q24 q23 q25
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q0 q9
tof q1 q10
tof q2 q12
tof q3 q14
tof q4 q16
tof q5 q18
tof q6 q20
tof q7 q22
tof q8 q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
tof q9 q10 q11
tof q12 q11 q13
tof q14 q13 q15
tof q16 q15 q17
tof q18 q17 q19
tof q20 q19 q21
tof q22 q21 q23
Z q23 q24
tof q22 q21 q23
tof q20 q19 q21
tof q18 q17 q19
tof q16 q15 q17
tof q14 q13 q15
tof q12 q11 q13
tof q9 q10 q11
tof q9
tof q10
tof q12
tof q14
tof q16
tof q18
tof q20
tof q22
tof q24
H q9
H q10
H q12
H q14
H q16
H q18
H q20
H q22
H q24
tof q0
tof q1
tof q2
tof q3
tof q4
tof q5
tof q6
tof q7
tof q8
H q26
END
