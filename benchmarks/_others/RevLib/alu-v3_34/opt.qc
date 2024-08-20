# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/alu-v3_34/circuit.qc):
#   Qubits: 5
#   H: 6
#   T: 21
#   X: 1
#   cnot: 21
#   Depth: 27
#   T depth: 12
# Result (0.338ms):
#   Qubits: 5
#   H: 6
#   T: 21
#   X: 1
#   cnot: 21
#   Depth: 27
#   T depth: 12
.v q0 q1 q2 q3 q4
.i q0 q1 q2 q3 q4
.o q0 q1 q2 q3 q4
BEGIN 
tof q4 q2 q1
tof q2
tof q4 q3
tof q1 q4 q2
tof q2 q0
tof q0 q3 q2
tof q2 q3
END
