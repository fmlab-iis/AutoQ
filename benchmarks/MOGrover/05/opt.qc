# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/MOGrover/5/circuit.qc):
#   Qubits: 15
#   H: 158
#   T: 392
#   X: 41
#   cnot: 380
#   cz: 4
#   Depth: 461
#   T depth: 184
# Result (3.463ms):
#   Qubits: 15
#   H: 158
#   T: 392
#   X: 41
#   cnot: 380
#   cz: 4
#   Depth: 461
#   T depth: 184
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
BEGIN 
tof q14
H q5
H q6
H q8
H q10
H q12
H q14
tof q0 q5
tof q1 q6
tof q2 q8
tof q3 q10
tof q4 q12
tof q5 q6 q7
tof q8 q7 q9
tof q10 q9 q11
tof q12 q11 q13
tof q13 q14
tof q12 q11 q13
tof q10 q9 q11
tof q8 q7 q9
tof q5 q6 q7
tof q0 q5
tof q1 q6
tof q2 q8
tof q3 q10
tof q4 q12
H q5
H q6
H q8
H q10
H q12
tof q5
tof q6
tof q8
tof q10
tof q12
tof q5 q6 q7
tof q8 q7 q9
tof q10 q9 q11
Z q11 q12
tof q10 q9 q11
tof q8 q7 q9
tof q5 q6 q7
tof q5
tof q6
tof q8
tof q10
tof q12
H q5
H q6
H q8
H q10
H q12
tof q0 q5
tof q1 q6
tof q2 q8
tof q3 q10
tof q4 q12
tof q5 q6 q7
tof q8 q7 q9
tof q10 q9 q11
tof q12 q11 q13
tof q13 q14
tof q12 q11 q13
tof q10 q9 q11
tof q8 q7 q9
tof q5 q6 q7
tof q0 q5
tof q1 q6
tof q2 q8
tof q3 q10
tof q4 q12
H q5
H q6
H q8
H q10
H q12
tof q5
tof q6
tof q8
tof q10
tof q12
tof q5 q6 q7
tof q8 q7 q9
tof q10 q9 q11
Z q11 q12
tof q10 q9 q11
tof q8 q7 q9
tof q5 q6 q7
tof q5
tof q6
tof q8
tof q10
tof q12
H q5
H q6
H q8
H q10
H q12
tof q0 q5
tof q1 q6
tof q2 q8
tof q3 q10
tof q4 q12
tof q5 q6 q7
tof q8 q7 q9
tof q10 q9 q11
tof q12 q11 q13
tof q13 q14
tof q12 q11 q13
tof q10 q9 q11
tof q8 q7 q9
tof q5 q6 q7
tof q0 q5
tof q1 q6
tof q2 q8
tof q3 q10
tof q4 q12
H q5
H q6
H q8
H q10
H q12
tof q5
tof q6
tof q8
tof q10
tof q12
tof q5 q6 q7
tof q8 q7 q9
tof q10 q9 q11
Z q11 q12
tof q10 q9 q11
tof q8 q7 q9
tof q5 q6 q7
tof q5
tof q6
tof q8
tof q10
tof q12
H q5
H q6
H q8
H q10
H q12
tof q0 q5
tof q1 q6
tof q2 q8
tof q3 q10
tof q4 q12
tof q5 q6 q7
tof q8 q7 q9
tof q10 q9 q11
tof q12 q11 q13
tof q13 q14
tof q12 q11 q13
tof q10 q9 q11
tof q8 q7 q9
tof q5 q6 q7
tof q0 q5
tof q1 q6
tof q2 q8
tof q3 q10
tof q4 q12
H q5
H q6
H q8
H q10
H q12
tof q5
tof q6
tof q8
tof q10
tof q12
tof q5 q6 q7
tof q8 q7 q9
tof q10 q9 q11
Z q11 q12
tof q10 q9 q11
tof q8 q7 q9
tof q5 q6 q7
tof q5
tof q6
tof q8
tof q10
tof q12
H q5
H q6
H q8
H q10
H q12
END
