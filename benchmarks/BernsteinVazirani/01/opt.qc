# Feynman -- quantum circuit toolkit
# Original (./01/circuit.qc):
#   Qubits: 2
#   H: 4
#   Z: 1
#   cnot: 1
#   Depth: 4
#   T depth: 0
# Result (0.259ms):
#   Qubits: 2
#   H: 4
#   Z: 1
#   cnot: 1
#   Depth: 4
#   T depth: 0
.v q0 q1
.i q0 q1
.o q0 q1
BEGIN 
H q0
H q1
Z q1
tof q0 q1
H q0
H q1
END
