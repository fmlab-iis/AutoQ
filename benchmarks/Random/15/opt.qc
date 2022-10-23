# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/15/circuit.qc):
#   Qubits: 15
#   H: 31
#   S: 10
#   T: 59
#   X: 7
#   Y: 4
#   Z: 4
#   cnot: 50
#   cz: 5
#   Depth: 50
#   T depth: 22
# Result (1.093ms):
#   Qubits: 15
#   H: 31
#   S: 10
#   T: 59
#   X: 7
#   Y: 4
#   Z: 4
#   cnot: 50
#   cz: 5
#   Depth: 50
#   T depth: 22
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
BEGIN 
tof q10
Z q11
H q0
S q0
H q0
Y q6
X q2
H q2
H q4
S q4
H q4
H q5
S q5
H q5
S q7
tof q9 q10 q3
H q13
S q13
H q13
Z q8 q2
X q0
H q0
T q14
tof q12
S q14
tof q0 q12
tof q4 q3 q8
tof q5 q13 q4
tof q12 q3 q11
Z q13 q14
Z q12
T q0
Z q2 q0
Z q1
S q9
tof q11 q13 q8
Z q9
tof q11 q7 q0
Y q3
S q13
Z q6 q3
tof q12
X q9
H q9
tof q11 q0 q1
tof q4
H q0
S q14
Y q11
H q3
S q3
H q3
tof q6 q7 q2
H q7
T q2
Z q1 q0
tof q4 q5
Y q0
END
