# Feynman -- quantum circuit toolkit
# Original (./07/circuit.qc):
#   Qubits: 8
#   H: 16
#   Z: 1
#   cnot: 4
#   Depth: 7
#   T depth: 0
# Result (0.499ms):
#   Qubits: 8
#   H: 16
#   Z: 1
#   cnot: 4
#   Depth: 7
#   T depth: 0
.v q0 q1 q2 q3 q4 q5 q6 q7
.i q0 q1 q2 q3 q4 q5 q6 q7
.o q0 q1 q2 q3 q4 q5 q6 q7
BEGIN 
H q0
H q1
H q2
H q3
H q4
H q5
H q6
H q7
Z q7
tof q0 q7
tof q2 q7
tof q4 q7
tof q6 q7
H q0
H q1
H q2
H q3
H q4
H q5
H q6
H q7
END
