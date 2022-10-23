# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/ex1_226/circuit.qc):
#   Qubits: 6
#   X: 2
#   cnot: 5
#   Depth: 5
#   T depth: 0
# Result (0.343ms):
#   Qubits: 6
#   X: 2
#   cnot: 5
#   Depth: 5
#   T depth: 0
.v q0 q1 q2 q3 q4 q5
.i q0 q1 q2 q3 q4 q5
.o q0 q1 q2 q3 q4 q5
BEGIN 
tof q3 q0
tof q1 q0
tof q5 q0
tof q2
tof q2 q0
tof q4
tof q4 q0
END
