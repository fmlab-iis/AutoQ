# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/MCToffoli/5/circuit.qc):
#   Qubits: 10
#   H: 16
#   T: 56
#   cnot: 49
#   Depth: 62
#   T depth: 26
# Result (0.392ms):
#   Qubits: 10
#   H: 16
#   T: 56
#   cnot: 49
#   Depth: 62
#   T depth: 26
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
BEGIN 
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q8 q9
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
END
