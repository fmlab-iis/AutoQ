# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/decod24-enable_125/circuit.qc):
#   Qubits: 6
#   H: 6
#   T: 21
#   cnot: 24
#   Depth: 28
#   T depth: 11
# Result (0.419ms):
#   Qubits: 6
#   H: 6
#   T: 21
#   cnot: 24
#   Depth: 28
#   T depth: 11
.v q0 q1 q2 q3 q4 q5
.i q0 q1 q2 q3 q4 q5
.o q0 q1 q2 q3 q4 q5
BEGIN 
tof q3 q2
tof q0 q2 q3
tof q3 q2
tof q2 q4
tof q1 q4 q2
tof q2 q4
tof q3 q5
tof q1 q5 q3
tof q3 q5
END
