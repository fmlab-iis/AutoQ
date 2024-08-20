# Feynman -- quantum circuit toolkit
# Original (./04/circuit.qc):
#   Qubits: 5
#   H: 10
#   Z: 1
#   cnot: 2
#   Depth: 5
#   T depth: 0
# Result (0.267ms):
#   Qubits: 5
#   H: 10
#   Z: 1
#   cnot: 2
#   Depth: 5
#   T depth: 0
.v q0 q1 q2 q3 q4
.i q0 q1 q2 q3 q4
.o q0 q1 q2 q3 q4
BEGIN 
H q0
H q1
H q2
H q3
H q4
Z q4
tof q0 q4
tof q2 q4
H q0
H q1
H q2
H q3
H q4
END
