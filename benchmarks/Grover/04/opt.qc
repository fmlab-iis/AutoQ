# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Grover/4/circuit.qc):
#   Qubits: 8
#   H: 90
#   T: 210
#   X: 37
#   cnot: 183
#   cz: 3
#   Depth: 256
#   T depth: 102
# Result (2.530ms):
#   Qubits: 8
#   H: 90
#   T: 210
#   X: 37
#   cnot: 183
#   cz: 3
#   Depth: 256
#   T depth: 102
.v q0 q1 q2 q3 q4 q5 q6 q7
.i q0 q1 q2 q3 q4 q5 q6 q7
.o q0 q1 q2 q3 q4 q5 q6 q7
BEGIN 
tof q7
H q0
H q1
H q3
H q5
H q7
tof q3
tof q0
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q6 q7
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q3
tof q0
H q0
H q1
H q3
H q5
tof q0
tof q1
tof q3
tof q5
tof q0 q1 q2
tof q3 q2 q4
Z q4 q5
tof q3 q2 q4
tof q0 q1 q2
tof q0
tof q1
tof q3
tof q5
H q0
H q1
H q3
H q5
tof q3
tof q0
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q6 q7
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q3
tof q0
H q0
H q1
H q3
H q5
tof q0
tof q1
tof q3
tof q5
tof q0 q1 q2
tof q3 q2 q4
Z q4 q5
tof q3 q2 q4
tof q0 q1 q2
tof q0
tof q1
tof q3
tof q5
H q0
H q1
H q3
H q5
tof q3
tof q0
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q6 q7
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q3
tof q0
H q0
H q1
H q3
H q5
tof q0
tof q1
tof q3
tof q5
tof q0 q1 q2
tof q3 q2 q4
Z q4 q5
tof q3 q2 q4
tof q0 q1 q2
tof q0
tof q1
tof q3
tof q5
H q0
H q1
H q3
H q5
H q7
END
