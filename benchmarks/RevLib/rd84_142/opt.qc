# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/rd84_142/circuit.qc):
#   Qubits: 15
#   H: 42
#   T: 147
#   cnot: 133
#   Depth: 93
#   T depth: 42
# Result (0.938ms):
#   Qubits: 15
#   H: 42
#   T: 147
#   cnot: 133
#   Depth: 93
#   T depth: 42
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
BEGIN 
tof q0 q1 q8
tof q0 q1
tof q2 q8 q9
tof q1 q2 q8
tof q1 q2
tof q3 q9 q10
tof q3 q8 q9
tof q2 q3 q8
tof q2 q3
tof q4 q10 q11
tof q4 q9 q10
tof q4 q8 q9
tof q3 q4 q8
tof q3 q4
tof q5 q11 q12
tof q5 q9 q10
tof q5 q8 q9
tof q4 q5 q8
tof q4 q5
tof q6 q12 q13
tof q6 q9 q10
tof q6 q8 q9
tof q5 q6 q8
tof q5 q6
tof q7 q13 q14
tof q7 q9 q10
tof q6 q7 q8
tof q6 q7
END
