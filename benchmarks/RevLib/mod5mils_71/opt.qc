# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/mod5mils_71/circuit.qc):
#   Qubits: 5
#   H: 4
#   T: 14
#   X: 1
#   cnot: 14
#   Depth: 18
#   T depth: 7
# Result (0.312ms):
#   Qubits: 5
#   H: 4
#   T: 14
#   X: 1
#   cnot: 14
#   Depth: 18
#   T depth: 7
.v q0 q1 q2 q3 q4
.i q0 q1 q2 q3 q4
.o q0 q1 q2 q3 q4
BEGIN 
tof q3
tof q1 q3
tof q2 q3 q4
tof q0 q3 q4
tof q3 q4
END
