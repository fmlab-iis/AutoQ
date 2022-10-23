# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/one-two-three-v3_101/circuit.qc):
#   Qubits: 5
#   H: 8
#   T: 28
#   cnot: 28
#   Depth: 35
#   T depth: 16
# Result (0.203ms):
#   Qubits: 5
#   H: 8
#   T: 28
#   cnot: 28
#   Depth: 35
#   T depth: 16
.v q0 q1 q2 q3 q4
.i q0 q1 q2 q3 q4
.o q0 q1 q2 q3 q4
BEGIN 
tof q3 q1
tof q2 q0
tof q4 q3 q2
tof q2 q0 q4
tof q4 q3
tof q3 q1 q4
tof q3 q2
tof q2 q0 q3
END
