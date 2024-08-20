# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Grover/5/circuit.qc):
#   Qubits: 10
#   H: 159
#   T: 392
#   X: 65
#   cnot: 340
#   cz: 4
#   Depth: 461
#   T depth: 184
# Result (3.082ms):
#   Qubits: 10
#   H: 159
#   T: 392
#   X: 65
#   cnot: 340
#   cz: 4
#   Depth: 461
#   T depth: 184
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
BEGIN 
tof q9
H q0
H q1
H q3
H q5
H q7
H q9
tof q7
tof q3
tof q0
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q8 q9
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
tof q0
tof q1
tof q3
tof q5
tof q7
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
Z q6 q7
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q0
tof q1
tof q3
tof q5
tof q7
H q0
H q1
H q3
H q5
H q7
tof q7
tof q3
tof q0
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q8 q9
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
tof q0
tof q1
tof q3
tof q5
tof q7
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
Z q6 q7
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q0
tof q1
tof q3
tof q5
tof q7
H q0
H q1
H q3
H q5
H q7
tof q7
tof q3
tof q0
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q8 q9
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
tof q0
tof q1
tof q3
tof q5
tof q7
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
Z q6 q7
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q0
tof q1
tof q3
tof q5
tof q7
H q0
H q1
H q3
H q5
H q7
tof q7
tof q3
tof q0
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q8 q9
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
tof q0
tof q1
tof q3
tof q5
tof q7
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
Z q6 q7
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q0
tof q1
tof q3
tof q5
tof q7
H q0
H q1
H q3
H q5
H q7
H q9
END
