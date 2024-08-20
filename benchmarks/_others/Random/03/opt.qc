# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/3/circuit.qc):
#   Qubits: 3
#   H: 8
#   S: 3
#   T: 7
#   X: 1
#   Y: 1
#   cnot: 7
#   Depth: 17
#   T depth: 4
# Result (0.447ms):
#   Qubits: 3
#   H: 8
#   S: 3
#   T: 7
#   X: 1
#   Y: 1
#   cnot: 7
#   Depth: 17
#   T depth: 4
.v q0 q1 q2
.i q0 q1 q2
.o q0 q1 q2
BEGIN 
H q1
S q1
H q1
H q1
S q1
H q1
Y q1
tof q0
H q1
tof q1 q2
H q2
S q0
tof q1 q2 q0
END
