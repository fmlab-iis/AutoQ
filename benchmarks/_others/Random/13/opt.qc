# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/13/circuit.qc):
#   Qubits: 13
#   H: 20
#   S: 7
#   T: 18
#   X: 11
#   Y: 3
#   Z: 1
#   cnot: 16
#   cz: 2
#   Depth: 24
#   T depth: 8
# Result (0.415ms):
#   Qubits: 13
#   H: 20
#   S: 7
#   T: 18
#   X: 11
#   Y: 3
#   Z: 1
#   cnot: 16
#   cz: 2
#   Depth: 24
#   T depth: 8
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
BEGIN 
Z q8
T q4
tof q10 q2
tof q12
S q5
X q8
H q8
H q4
tof q3 q5
H q10
H q6
S q6
H q6
X q4
H q4
tof q8 q1
Y q2
Z q11 q7
tof q4 q0 q1
X q2
H q2
H q3
X q2
H q2
X q3
H q3
T q7
tof q6 q1
tof q3
X q9
H q9
X q8
H q8
T q5
tof q9
T q9
Y q3
S q0
tof q6
H q8
S q8
H q8
tof q8 q3 q6
H q8
S q8
S q2
Y q0
Z q1 q9
H q9
S q9
END
