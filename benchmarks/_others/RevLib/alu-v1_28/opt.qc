# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/alu-v1_28/circuit.qc):
#   Qubits: 5
#   H: 4
#   T: 14
#   X: 1
#   cnot: 16
#   Depth: 20
#   T depth: 8
# Result (0.326ms):
#   Qubits: 5
#   H: 4
#   T: 14
#   X: 1
#   cnot: 16
#   Depth: 20
#   T depth: 8
.v q0 q1 q2 q3 q4
.i q0 q1 q2 q3 q4
.o q0 q1 q2 q3 q4
BEGIN 
tof q4 q3
tof q1 q2
tof q2 q4
tof q4 q2 q1
tof q1 q0
tof q0 q3 q1
tof q1
END
