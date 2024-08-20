# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/5/circuit.qc):
#   Qubits: 5
#   H: 8
#   S: 4
#   T: 8
#   X: 3
#   Z: 2
#   cnot: 6
#   cz: 2
#   Depth: 16
#   T depth: 5
# Result (0.563ms):
#   Qubits: 5
#   H: 8
#   S: 4
#   T: 8
#   X: 3
#   Z: 2
#   cnot: 6
#   cz: 2
#   Depth: 16
#   T depth: 5
.v q0 q1 q2 q3 q4
.i q0 q1 q2 q3 q4
.o q0 q1 q2 q3 q4
BEGIN 
Z q1
H q2
S q2
H q2
T q1
X q0
H q0
S q4
H q1
Z q1 q4
S q2
tof q0
Z q0 q4
tof q4 q3 q0
X q3
H q3
S q3
H q4
Z q1
END
