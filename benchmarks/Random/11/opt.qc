# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/11/circuit.qc):
#   Qubits: 11
#   H: 15
#   S: 1
#   T: 34
#   X: 8
#   Y: 3
#   Z: 2
#   cnot: 27
#   cz: 3
#   Depth: 34
#   T depth: 14
# Result (0.888ms):
#   Qubits: 11
#   H: 15
#   S: 1
#   T: 34
#   X: 8
#   Y: 3
#   Z: 2
#   cnot: 27
#   cz: 3
#   Depth: 34
#   T depth: 14
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
BEGIN 
T q8
Z q7 q8
X q7
H q7
T q3
T q9
T q10
tof q7 q0 q9
tof q9 q10 q3
tof q10 q1
H q7
Z q3
tof q2
tof q6 q0
H q4
X q10
H q10
Z q8 q2
T q3
Y q4
tof q10 q0
X q7
H q7
tof q10
S q8
X q3
H q3
tof q2
T q3
tof q7
Z q6 q1
tof q0 q6 q9
H q0
tof q2 q3 q5
Z q3
Y q9
Y q9
END
