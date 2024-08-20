# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Grover/2/circuit.qc):
#   Qubits: 3
#   H: 10
#   T: 7
#   X: 7
#   cnot: 6
#   cz: 1
#   Depth: 16
#   T depth: 4
# Result (0.506ms):
#   Qubits: 3
#   H: 10
#   T: 7
#   X: 7
#   cnot: 6
#   cz: 1
#   Depth: 16
#   T depth: 4
.v q0 q1 q2
.i q0 q1 q2
.o q0 q1 q2
BEGIN 
tof q2
H q0
H q1
H q2
tof q0
tof q0 q1 q2
tof q0
H q0
H q1
tof q0
tof q1
Z q0 q1
tof q0
tof q1
H q0
H q1
H q2
END
