# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/ex-1_166/circuit.qc):
#   Qubits: 3
#   H: 2
#   T: 7
#   X: 1
#   cnot: 8
#   Depth: 11
#   T depth: 4
# Result (0.245ms):
#   Qubits: 3
#   H: 2
#   T: 7
#   X: 1
#   cnot: 8
#   Depth: 11
#   T depth: 4
.v q0 q1 q2
.i q0 q1 q2
.o q0 q1 q2
BEGIN 
tof q0 q1
tof q1 q2 q0
tof q0 q1
tof q0
END
