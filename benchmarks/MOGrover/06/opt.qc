# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/MOGrover/6/circuit.qc):
#   Qubits: 18
#   H: 295
#   T: 756
#   X: 73
#   cnot: 726
#   cz: 6
#   Depth: 871
#   T depth: 348
# Result (4.979ms):
#   Qubits: 18
#   H: 295
#   T: 756
#   X: 73
#   cnot: 726
#   cz: 6
#   Depth: 871
#   T depth: 348
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
BEGIN 
tof q17
H q6
H q7
H q9
H q11
H q13
H q15
H q17
tof q0 q6
tof q1 q7
tof q2 q9
tof q3 q11
tof q4 q13
tof q5 q15
tof q6 q7 q8
tof q9 q8 q10
tof q11 q10 q12
tof q13 q12 q14
tof q15 q14 q16
tof q16 q17
tof q15 q14 q16
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q6 q7 q8
tof q0 q6
tof q1 q7
tof q2 q9
tof q3 q11
tof q4 q13
tof q5 q15
H q6
H q7
H q9
H q11
H q13
H q15
tof q6
tof q7
tof q9
tof q11
tof q13
tof q15
tof q6 q7 q8
tof q9 q8 q10
tof q11 q10 q12
tof q13 q12 q14
Z q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q6 q7 q8
tof q6
tof q7
tof q9
tof q11
tof q13
tof q15
H q6
H q7
H q9
H q11
H q13
H q15
tof q0 q6
tof q1 q7
tof q2 q9
tof q3 q11
tof q4 q13
tof q5 q15
tof q6 q7 q8
tof q9 q8 q10
tof q11 q10 q12
tof q13 q12 q14
tof q15 q14 q16
tof q16 q17
tof q15 q14 q16
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q6 q7 q8
tof q0 q6
tof q1 q7
tof q2 q9
tof q3 q11
tof q4 q13
tof q5 q15
H q6
H q7
H q9
H q11
H q13
H q15
tof q6
tof q7
tof q9
tof q11
tof q13
tof q15
tof q6 q7 q8
tof q9 q8 q10
tof q11 q10 q12
tof q13 q12 q14
Z q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q6 q7 q8
tof q6
tof q7
tof q9
tof q11
tof q13
tof q15
H q6
H q7
H q9
H q11
H q13
H q15
tof q0 q6
tof q1 q7
tof q2 q9
tof q3 q11
tof q4 q13
tof q5 q15
tof q6 q7 q8
tof q9 q8 q10
tof q11 q10 q12
tof q13 q12 q14
tof q15 q14 q16
tof q16 q17
tof q15 q14 q16
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q6 q7 q8
tof q0 q6
tof q1 q7
tof q2 q9
tof q3 q11
tof q4 q13
tof q5 q15
H q6
H q7
H q9
H q11
H q13
H q15
tof q6
tof q7
tof q9
tof q11
tof q13
tof q15
tof q6 q7 q8
tof q9 q8 q10
tof q11 q10 q12
tof q13 q12 q14
Z q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q6 q7 q8
tof q6
tof q7
tof q9
tof q11
tof q13
tof q15
H q6
H q7
H q9
H q11
H q13
H q15
tof q0 q6
tof q1 q7
tof q2 q9
tof q3 q11
tof q4 q13
tof q5 q15
tof q6 q7 q8
tof q9 q8 q10
tof q11 q10 q12
tof q13 q12 q14
tof q15 q14 q16
tof q16 q17
tof q15 q14 q16
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q6 q7 q8
tof q0 q6
tof q1 q7
tof q2 q9
tof q3 q11
tof q4 q13
tof q5 q15
H q6
H q7
H q9
H q11
H q13
H q15
tof q6
tof q7
tof q9
tof q11
tof q13
tof q15
tof q6 q7 q8
tof q9 q8 q10
tof q11 q10 q12
tof q13 q12 q14
Z q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q6 q7 q8
tof q6
tof q7
tof q9
tof q11
tof q13
tof q15
H q6
H q7
H q9
H q11
H q13
H q15
tof q0 q6
tof q1 q7
tof q2 q9
tof q3 q11
tof q4 q13
tof q5 q15
tof q6 q7 q8
tof q9 q8 q10
tof q11 q10 q12
tof q13 q12 q14
tof q15 q14 q16
tof q16 q17
tof q15 q14 q16
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q6 q7 q8
tof q0 q6
tof q1 q7
tof q2 q9
tof q3 q11
tof q4 q13
tof q5 q15
H q6
H q7
H q9
H q11
H q13
H q15
tof q6
tof q7
tof q9
tof q11
tof q13
tof q15
tof q6 q7 q8
tof q9 q8 q10
tof q11 q10 q12
tof q13 q12 q14
Z q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q6 q7 q8
tof q6
tof q7
tof q9
tof q11
tof q13
tof q15
H q6
H q7
H q9
H q11
H q13
H q15
tof q0 q6
tof q1 q7
tof q2 q9
tof q3 q11
tof q4 q13
tof q5 q15
tof q6 q7 q8
tof q9 q8 q10
tof q11 q10 q12
tof q13 q12 q14
tof q15 q14 q16
tof q16 q17
tof q15 q14 q16
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q6 q7 q8
tof q0 q6
tof q1 q7
tof q2 q9
tof q3 q11
tof q4 q13
tof q5 q15
H q6
H q7
H q9
H q11
H q13
H q15
tof q6
tof q7
tof q9
tof q11
tof q13
tof q15
tof q6 q7 q8
tof q9 q8 q10
tof q11 q10 q12
tof q13 q12 q14
Z q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q6 q7 q8
tof q6
tof q7
tof q9
tof q11
tof q13
tof q15
H q6
H q7
H q9
H q11
H q13
H q15
END
