# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/decod24-v0_38/circuit.qc):
#   Qubits: 4
#   H: 6
#   T: 21
#   X: 1
#   cnot: 20
#   Depth: 27
#   T depth: 12
# Result (0.301ms):
#   Qubits: 4
#   H: 6
#   T: 21
#   X: 1
#   cnot: 20
#   Depth: 27
#   T depth: 12
.v q0 q1 q2 q3
.i q0 q1 q2 q3
.o q0 q1 q2 q3
BEGIN 
tof q3 q2 q0
tof q2 q3
tof q3 q2 q1
tof q2 q0 q3
tof q3 q2
tof q3
END
