# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/4mod5-bdd_287/circuit.qc):
#   Qubits: 7
#   H: 8
#   T: 28
#   X: 1
#   cnot: 27
#   Depth: 34
#   T depth: 15
# Result (0.386ms):
#   Qubits: 7
#   H: 8
#   T: 28
#   X: 1
#   cnot: 27
#   Depth: 34
#   T depth: 15
.v q0 q1 q2 q3 q4 q5 q6
.i q0 q1 q2 q3 q4 q5 q6
.o q0 q1 q2 q3 q4 q5 q6
BEGIN 
tof q3 q4
tof q1 q4
tof q0 q4 q5
tof q0 q4 q6
tof q4 q6
tof q6
tof q2 q6 q5
tof q2 q5 q6
END
