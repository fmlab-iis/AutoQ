# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/7/circuit.qc):
#   Qubits: 7
#   H: 8
#   S: 6
#   T: 9
#   X: 4
#   Z: 1
#   cnot: 9
#   cz: 2
#   Depth: 18
#   T depth: 4
# Result (0.673ms):
#   Qubits: 7
#   H: 8
#   S: 6
#   T: 9
#   X: 4
#   Z: 1
#   cnot: 9
#   cz: 2
#   Depth: 18
#   T depth: 4
.v q0 q1 q2 q3 q4 q5 q6
.i q0 q1 q2 q3 q4 q5 q6
.o q0 q1 q2 q3 q4 q5 q6
BEGIN 
X q3
H q3
tof q4 q5
T q5
X q0
H q0
tof q1 q2 q0
tof q3
H q6
tof q2
T q3
S q1
H q0
S q0
H q0
Z q1
Z q0 q2
Z q0 q6
H q2
tof q1 q0
S q0
tof q1 q2
S q5
S q3
S q1
END
