# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/mod5d2_70/circuit.qc):
#   Qubits: 5
#   H: 4
#   T: 14
#   X: 2
#   cnot: 16
#   Depth: 20
#   T depth: 8
# Result (0.384ms):
#   Qubits: 5
#   H: 4
#   T: 14
#   X: 2
#   cnot: 16
#   Depth: 20
#   T depth: 8
.v q0 q1 q2 q3 q4
.i q0 q1 q2 q3 q4
.o q0 q1 q2 q3 q4
BEGIN 
tof q4
tof q3
tof q3 q2
tof q3 q1
tof q4 q3
tof q1 q3 q0
tof q1 q2 q0
tof q2 q1
END
