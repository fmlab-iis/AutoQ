# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/4/circuit.qc):
#   Qubits: 4
#   H: 9
#   S: 3
#   T: 14
#   X: 5
#   Z: 1
#   cnot: 13
#   Depth: 24
#   T depth: 8
# Result (0.373ms):
#   Qubits: 4
#   H: 9
#   S: 3
#   T: 14
#   X: 5
#   Z: 1
#   cnot: 13
#   Depth: 24
#   T depth: 8
.v q0 q1 q2 q3
.i q0 q1 q2 q3
.o q0 q1 q2 q3
BEGIN 
tof q2
H q2
S q2
H q2
tof q3 q1 q2
tof q2 q1 q3
X q0
H q0
Z q2
X q1
H q1
S q3
tof q1
S q0
X q2
H q2
tof q2 q3
END
