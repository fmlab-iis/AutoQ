# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/sym6_316/circuit.qc):
#   Qubits: 14
#   H: 32
#   T: 112
#   X: 2
#   cnot: 107
#   Depth: 120
#   T depth: 52
# Result (1.017ms):
#   Qubits: 14
#   H: 32
#   T: 112
#   X: 2
#   cnot: 107
#   Depth: 120
#   T depth: 52
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
BEGIN 
tof q0 q6
tof q0 q5 q6
tof q5 q6
tof q0 q5 q7
tof q7 q8
tof q4 q6 q8
tof q4 q7 q8
tof q4 q7 q9
tof q9 q10
tof q1 q8 q10
tof q1 q9 q10
tof q4 q11
tof q4 q6 q11
tof q6 q11
tof q1 q12
tof q11 q12
tof q1 q9 q12
tof q1 q11 q12
tof q12 q13
tof q3 q10 q13
tof q3 q12 q13
tof q8 q11
tof q1 q11 q8
tof q8
tof q3 q8 q12
tof q3 q12 q8
tof q8 q13
tof q2 q13 q8
tof q8
END
