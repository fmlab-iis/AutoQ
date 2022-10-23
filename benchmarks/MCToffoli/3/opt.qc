# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/MCToffoli/3/circuit.qc):
#   Qubits: 6
#   H: 8
#   T: 28
#   cnot: 25
#   Depth: 32
#   T depth: 14
# Result (0.285ms):
#   Qubits: 6
#   H: 8
#   T: 28
#   cnot: 25
#   Depth: 32
#   T depth: 14
.v q0 q1 q2 q3 q4 q5
.i q0 q1 q2 q3 q4 q5
.o q0 q1 q2 q3 q4 q5
BEGIN 
tof q0 q1 q2
tof q3 q2 q4
tof q4 q5
tof q3 q2 q4
tof q0 q1 q2
END
