# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/0410184_169/circuit.qc):
#   Qubits: 14
#   H: 22
#   T: 77
#   X: 8
#   cnot: 93
#   Depth: 93
#   T depth: 39
# Result (1.043ms):
#   Qubits: 14
#   H: 22
#   T: 77
#   X: 8
#   cnot: 93
#   Depth: 93
#   T depth: 39
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
BEGIN 
tof q4 q3
tof q6 q5
tof q8 q7
tof q10 q9
tof q12 q11
tof q4 q2
tof q0 q1 q2
tof q6 q4
tof q2 q3 q4
tof q8 q6
tof q4 q5 q6
tof q10 q8
tof q6 q7 q8
tof q12 q10
tof q8 q9 q10
tof q12 q13
tof q3
tof q5
tof q7
tof q9
tof q10 q11 q13
tof q2 q3
tof q4 q5
tof q6 q7
tof q8 q9
tof q10 q11
tof q8 q9 q10
tof q6 q7 q8
tof q9
tof q12 q10
tof q4 q5 q6
tof q7
tof q10 q8
tof q2 q3 q4
tof q5
tof q8 q6
tof q0 q1 q2
tof q3
tof q6 q4
tof q4 q2
tof q1 q0
tof q4 q3
tof q6 q5
tof q8 q7
tof q10 q9
tof q12 q11
END
