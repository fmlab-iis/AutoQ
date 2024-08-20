# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/4gt11_83/circuit.qc):
#   Qubits: 5
#   H: 2
#   T: 7
#   cnot: 13
#   Depth: 14
#   T depth: 4
# Result (0.314ms):
#   Qubits: 5
#   H: 2
#   T: 7
#   cnot: 13
#   Depth: 14
#   T depth: 4
.v q0 q1 q2 q3 q4
.i q0 q1 q2 q3 q4
.o q0 q1 q2 q3 q4
BEGIN 
tof q2 q1
tof q1 q2
tof q3 q2
tof q2 q3
tof q4 q3
tof q3 q4
tof q1 q4 q0
tof q0 q4
END
