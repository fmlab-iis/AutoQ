# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Grover/3/circuit.qc):
#   Qubits: 6
#   H: 41
#   T: 84
#   X: 21
#   cnot: 74
#   cz: 2
#   Depth: 111
#   T depth: 44
# Result (1.157ms):
#   Qubits: 6
#   H: 41
#   T: 84
#   X: 21
#   cnot: 74
#   cz: 2
#   Depth: 111
#   T depth: 44
.v q0 q1 q2 q3 q4 q5
.i q0 q1 q2 q3 q4 q5
.o q0 q1 q2 q3 q4 q5
BEGIN 
tof q5
H q0
H q1
H q3
H q5
tof q3
tof q0
tof q0 q1 q2
tof q3 q2 q4
tof q4 q5
tof q3 q2 q4
tof q0 q1 q2
tof q3
tof q0
H q0
H q1
H q3
tof q0
tof q1
tof q3
tof q0 q1 q2
Z q2 q3
tof q0 q1 q2
tof q0
tof q1
tof q3
H q0
H q1
H q3
tof q3
tof q0
tof q0 q1 q2
tof q3 q2 q4
tof q4 q5
tof q3 q2 q4
tof q0 q1 q2
tof q3
tof q0
H q0
H q1
H q3
tof q0
tof q1
tof q3
tof q0 q1 q2
Z q2 q3
tof q0 q1 q2
tof q0
tof q1
tof q3
H q0
H q1
H q3
H q5
END
