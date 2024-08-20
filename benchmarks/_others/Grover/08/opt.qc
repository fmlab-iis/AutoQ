# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Grover/8/circuit.qc):
#   Qubits: 16
#   H: 826
#   T: 2184
#   X: 289
#   cnot: 1884
#   cz: 12
#   Depth: 2461
#   T depth: 984
# Result (9.449ms):
#   Qubits: 16
#   H: 826
#   T: 2184
#   X: 289
#   cnot: 1884
#   cz: 12
#   Depth: 2461
#   T depth: 984
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
BEGIN 
tof q15
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
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
tof q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q11 q10 q12
Z q12 q13
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
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
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
tof q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q11 q10 q12
Z q12 q13
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
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
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
tof q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q11 q10 q12
Z q12 q13
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
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
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
tof q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q11 q10 q12
Z q12 q13
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
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
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
tof q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q11 q10 q12
Z q12 q13
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
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
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
tof q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q11 q10 q12
Z q12 q13
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
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
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
tof q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q11 q10 q12
Z q12 q13
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
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
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
tof q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q11 q10 q12
Z q12 q13
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
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
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
tof q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q11 q10 q12
Z q12 q13
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
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
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
tof q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q11 q10 q12
Z q12 q13
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
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
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
tof q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q11 q10 q12
Z q12 q13
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
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
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
tof q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
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
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q11
tof q13
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q11 q10 q12
Z q12 q13
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
H q0
H q1
H q3
H q5
H q7
H q9
H q11
H q13
H q15
END
