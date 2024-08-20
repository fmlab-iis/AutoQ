# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/4gt11-v1_85/circuit.qc):
#   Qubits: 5
#   H: 2
#   T: 7
#   X: 1
#   cnot: 8
#   Depth: 10
#   T depth: 4
# Result (0.254ms):
#   Qubits: 5
#   H: 2
#   T: 7
#   X: 1
#   cnot: 8
#   Depth: 10
#   T depth: 4
.v q0 q1 q2 q3 q4
.i q0 q1 q2 q3 q4
.o q0 q1 q2 q3 q4
BEGIN 
tof q4 q0
tof q4
tof q2 q1 q0
tof q0 q4
END
