# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/14/circuit.qc):
#   Qubits: 14
#   H: 23
#   S: 10
#   T: 31
#   X: 9
#   Y: 4
#   Z: 3
#   cnot: 27
#   cz: 3
#   Depth: 28
#   T depth: 8
# Result (0.994ms):
#   Qubits: 14
#   H: 23
#   S: 10
#   T: 31
#   X: 9
#   Y: 4
#   Z: 3
#   cnot: 27
#   cz: 3
#   Depth: 28
#   T depth: 8
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
BEGIN 
Z q12
X q2
H q2
tof q1
tof q7
S q11
H q1
S q1
H q1
T q0
tof q12 q9 q1
H q3
S q3
H q3
S q6
Y q13
H q6
Y q4
T q6
tof q12 q10
X q1
H q1
H q3
Y q6
Z q10
tof q13 q8 q2
Z q3 q11
H q11
S q11
H q11
S q5
S q12
tof q13 q4
X q1
H q1
tof q1 q7
tof q10
T q3
X q4
H q4
Y q12
tof q3 q6 q0
X q8
H q8
Z q13
S q3
X q1
H q1
H q11
tof q10 q1 q5
S q5
S q5
Z q3 q4
Z q9 q6
END
