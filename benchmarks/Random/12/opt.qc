# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/12/circuit.qc):
#   Qubits: 12
#   H: 21
#   S: 11
#   T: 22
#   X: 7
#   Y: 2
#   Z: 1
#   cnot: 22
#   cz: 6
#   Depth: 31
#   T depth: 8
# Result (0.985ms):
#   Qubits: 12
#   H: 21
#   S: 11
#   T: 22
#   X: 7
#   Y: 2
#   Z: 1
#   cnot: 22
#   cz: 6
#   Depth: 31
#   T depth: 8
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
BEGIN 
tof q5
H q0
S q0
H q0
X q1
H q1
H q7
S q7
H q7
H q4
S q4
H q4
Z q11 q5
tof q11 q4
Z q11 q0
S q10
Y q8
X q9
H q9
H q8
S q8
H q8
tof q6 q0 q9
S q5
tof q9
S q9
Z q3 q5
X q6
H q6
S q4
tof q2 q8
Y q2
tof q10
S q6
tof q6 q4
H q6
Z q6 q10
X q10
H q10
S q0
Z q1
tof q7 q8 q10
H q7
S q7
H q7
Z q2 q0
tof q2 q1
tof q2 q11 q5
T q9
Z q4 q10
END
