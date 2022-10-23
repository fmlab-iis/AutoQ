# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/alu-bdd_288/circuit.qc):
#   Qubits: 7
#   H: 10
#   T: 35
#   X: 1
#   cnot: 33
#   Depth: 43
#   T depth: 17
# Result (0.372ms):
#   Qubits: 7
#   H: 10
#   T: 35
#   X: 1
#   cnot: 33
#   Depth: 43
#   T depth: 17
.v q0 q1 q2 q3 q4 q5 q6
.i q0 q1 q2 q3 q4 q5 q6
.o q0 q1 q2 q3 q4 q5 q6
BEGIN 
tof q0 q5
tof q1 q3 q5
tof q0 q3 q5
tof q2 q6
tof q0 q3 q6
tof q2 q3 q6
tof q6 q5
tof q4 q5 q6
tof q6
END
