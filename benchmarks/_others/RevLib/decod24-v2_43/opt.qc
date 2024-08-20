# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/decod24-v2_43/circuit.qc):
#   Qubits: 4
#   H: 6
#   T: 21
#   X: 2
#   cnot: 19
#   Depth: 26
#   T depth: 12
# Result (0.299ms):
#   Qubits: 4
#   H: 6
#   T: 21
#   X: 2
#   cnot: 19
#   Depth: 26
#   T depth: 12
.v q0 q1 q2 q3
.i q0 q1 q2 q3
.o q0 q1 q2 q3
BEGIN 
tof q3 q2 q0
tof q2 q0 q3
tof q0 q2 q1
tof q3 q2
tof q0
tof q3
END
