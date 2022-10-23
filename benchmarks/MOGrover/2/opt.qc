# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/MOGrover/2/circuit.qc):
#   Qubits: 5
#   H: 9
#   T: 7
#   X: 5
#   cnot: 10
#   cz: 1
#   Depth: 15
#   T depth: 4
# Result (0.565ms):
#   Qubits: 5
#   H: 9
#   T: 7
#   X: 5
#   cnot: 10
#   cz: 1
#   Depth: 15
#   T depth: 4
.v q0 q1 q2 q3 q4
.i q0 q1 q2 q3 q4
.o q0 q1 q2 q3 q4
BEGIN 
tof q4
H q2
H q3
H q4
tof q0 q2
tof q1 q3
tof q0 q1 q2
tof q0 q2
tof q1 q3
H q2
H q3
tof q2
tof q3
Z q0 q1
tof q2
tof q3
H q2
H q3
END
