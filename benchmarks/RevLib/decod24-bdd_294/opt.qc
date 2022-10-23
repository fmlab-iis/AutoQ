# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/decod24-bdd_294/circuit.qc):
#   Qubits: 6
#   H: 8
#   T: 28
#   X: 3
#   cnot: 28
#   Depth: 36
#   T depth: 16
# Result (0.481ms):
#   Qubits: 6
#   H: 8
#   T: 28
#   X: 3
#   cnot: 28
#   Depth: 36
#   T depth: 16
.v q0 q1 q2 q3 q4 q5
.i q0 q1 q2 q3 q4 q5
.o q0 q1 q2 q3 q4 q5
BEGIN 
tof q0 q1 q2
tof q0 q1 q3
tof q0 q3
tof q0 q1 q4
tof q1 q4
tof q0 q5
tof q0 q1 q5
tof q1 q5
tof q3
tof q4
tof q5
END
