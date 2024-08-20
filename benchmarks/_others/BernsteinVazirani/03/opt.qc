# Feynman -- quantum circuit toolkit
# Original (./03/circuit.qc):
#   Qubits: 4
#   H: 8
#   Z: 1
#   cnot: 2
#   Depth: 5
#   T depth: 0
# Result (0.327ms):
#   Qubits: 4
#   H: 8
#   Z: 1
#   cnot: 2
#   Depth: 5
#   T depth: 0
.v q0 q1 q2 q3
.i q0 q1 q2 q3
.o q0 q1 q2 q3
BEGIN 
H q0
H q1
H q2
H q3
Z q3
tof q0 q3
tof q2 q3
H q0
H q1
H q2
H q3
END
