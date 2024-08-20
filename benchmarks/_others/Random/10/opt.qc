# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/10/circuit.qc):
#   Qubits: 10
#   H: 20
#   S: 5
#   T: 15
#   X: 6
#   Y: 1
#   Z: 3
#   cnot: 16
#   cz: 3
#   Depth: 24
#   T depth: 8
# Result (0.668ms):
#   Qubits: 10
#   H: 20
#   S: 5
#   T: 15
#   X: 6
#   Y: 1
#   Z: 3
#   cnot: 16
#   cz: 3
#   Depth: 24
#   T depth: 8
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
BEGIN 
S q2
tof q6
tof q3 q2
Z q5
Z q9 q1
H q9
tof q0 q7
X q8
H q8
tof q0 q4
tof q0 q4
X q9
H q9
H q1
H q4
Z q2
Z q0
H q5
S q5
H q5
tof q9 q0 q2
T q3
tof q0 q4 q9
X q9
H q9
Z q2 q5
H q4
S q4
H q4
Y q9
tof q6
Z q5 q0
tof q9
H q3
S q3
H q3
H q1
S q1
H q1
H q4
H q1
END
