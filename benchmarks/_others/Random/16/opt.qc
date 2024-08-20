# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/16/circuit.qc):
#   Qubits: 16
#   H: 22
#   S: 7
#   T: 18
#   X: 18
#   Y: 4
#   Z: 3
#   cnot: 14
#   cz: 5
#   Depth: 23
#   T depth: 7
# Result (1.136ms):
#   Qubits: 16
#   H: 22
#   S: 7
#   T: 18
#   X: 18
#   Y: 4
#   Z: 3
#   cnot: 14
#   cz: 5
#   Depth: 23
#   T depth: 7
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
BEGIN 
tof q5
X q6
H q6
tof q1 q11
tof q1
X q5
H q5
tof q7
T q9
tof q2
T q7
H q0
S q0
H q0
X q13
H q13
S q15
H q12
S q12
H q12
Y q15
tof q9
X q0
H q0
H q1
S q1
H q1
X q11
H q11
Z q6
tof q10 q11 q12
Z q11 q5
Z q13 q2
Y q7
S q4
T q12
H q5
X q7
H q7
X q2
H q2
Y q0
H q11
S q11
H q11
H q0
S q13
Z q3 q8
tof q15
Z q13 q5
T q10
tof q14
tof q9
tof q6
tof q7 q11 q13
H q0
tof q14
tof q2 q9
Z q2 q0
Z q8
Y q7
Z q3
tof q6
END
