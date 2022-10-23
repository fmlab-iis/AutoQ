# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/MCToffoli/4/circuit.qc):
#   Qubits: 8
#   H: 12
#   T: 42
#   cnot: 37
#   Depth: 47
#   T depth: 20
# Result (0.322ms):
#   Qubits: 8
#   H: 12
#   T: 42
#   cnot: 37
#   Depth: 47
#   T depth: 20
.v q0 q1 q2 q3 q4 q5 q6 q7
.i q0 q1 q2 q3 q4 q5 q6 q7
.o q0 q1 q2 q3 q4 q5 q6 q7
BEGIN 
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q6 q7
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
END
