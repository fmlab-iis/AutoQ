# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/9/circuit.qc):
#   Qubits: 9
#   H: 15
#   S: 10
#   T: 1
#   X: 5
#   Y: 6
#   Z: 1
#   cnot: 2
#   Depth: 9
#   T depth: 1
# Result (0.894ms):
#   Qubits: 9
#   H: 15
#   S: 10
#   T: 1
#   X: 5
#   Y: 6
#   Z: 1
#   cnot: 2
#   Depth: 9
#   T depth: 1
.v q0 q1 q2 q3 q4 q5 q6 q7 q8
.i q0 q1 q2 q3 q4 q5 q6 q7 q8
.o q0 q1 q2 q3 q4 q5 q6 q7 q8
BEGIN 
H q8
H q1
S q1
H q1
T q2
S q6
S q5
tof q3 q8
X q6
H q6
Z q2
S q6
X q0
H q0
tof q7
Y q7
S q7
S q2
Y q3
H q1
X q8
H q8
H q2
S q2
H q2
H q2
S q2
H q2
tof q7
Y q0
Y q6
tof q6 q4
Y q5
Y q4
H q3
S q3
H q3
H q5
S q5
H q5
END
