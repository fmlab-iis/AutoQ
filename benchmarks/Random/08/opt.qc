# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/8/circuit.qc):
#   Qubits: 8
#   H: 13
#   S: 1
#   T: 21
#   X: 3
#   Y: 5
#   Z: 5
#   cnot: 20
#   cz: 2
#   Depth: 28
#   T depth: 10
# Result (0.737ms):
#   Qubits: 8
#   H: 13
#   S: 1
#   T: 21
#   X: 3
#   Y: 5
#   Z: 5
#   cnot: 20
#   cz: 2
#   Depth: 28
#   T depth: 10
.v q0 q1 q2 q3 q4 q5 q6 q7
.i q0 q1 q2 q3 q4 q5 q6 q7
.o q0 q1 q2 q3 q4 q5 q6 q7
BEGIN 
Z q4 q3
Z q5
H q6
tof q0 q2
Y q0
tof q5 q4 q7
X q7
H q7
Y q3
Z q5
Z q6
Z q3
Y q2
X q2
H q2
tof q0 q5 q3
H q4
S q4
H q4
Y q3
H q4
tof q7 q2 q0
Y q6
tof q2
H q1
Z q2
tof q1 q0
Z q4 q2
END
