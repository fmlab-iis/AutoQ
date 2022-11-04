# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Grover/15/circuit.qc):
#   Qubits: 30
#   H: 19613
#   T: 53676
#   X: 6533
#   cnot: 46150
#   cz: 142
#   Depth: 58931
#   T depth: 23572
# Result (106.564ms):
#   Qubits: 30
#   H: 19613
#   T: 53676
#   X: 6533
#   cnot: 46150
#   cz: 142
#   Depth: 58931
#   T depth: 23572
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29
BEGIN 
tof q29
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
H q29
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
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
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
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
tof q27
tof q23
tof q19
tof q15
tof q11
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
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
tof q23 q22 q24
tof q25 q24 q26
Z q26 q27
tof q25 q24 q26
tof q23 q22 q24
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q15
tof q17
tof q19
tof q21
tof q23
tof q25
tof q27
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
H q17
H q19
H q21
H q23
H q25
H q27
H q29
END
