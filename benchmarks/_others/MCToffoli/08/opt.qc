# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/MCToffoli/8/circuit.qc):
#   Qubits: 16
#   H: 28
#   T: 98
#   cnot: 85
#   Depth: 107
#   T depth: 44
# Result (0.632ms):
#   Qubits: 16
#   H: 28
#   T: 98
#   cnot: 85
#   Depth: 107
#   T depth: 44
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
BEGIN 
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q11 q10 q12
tof q13 q12 q14
tof q14 q15
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
END
