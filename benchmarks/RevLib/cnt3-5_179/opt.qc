# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/cnt3-5_179/circuit.qc):
#   Qubits: 16
#   H: 20
#   T: 70
#   cnot: 75
#   Depth: 51
#   T depth: 20
# Result (0.915ms):
#   Qubits: 16
#   H: 20
#   T: 70
#   cnot: 75
#   Depth: 51
#   T depth: 20
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
BEGIN 
tof q12 q15
tof q14 q13 q12
tof q12 q15
tof q15 q13 q14
tof q13 q15
tof q9 q11
tof q10 q12 q9
tof q9 q11
tof q11 q12 q10
tof q12 q11
tof q6 q8
tof q7 q9 q6
tof q6 q8
tof q8 q9 q7
tof q9 q8
tof q3 q5
tof q4 q6 q3
tof q3 q5
tof q5 q6 q4
tof q6 q5
tof q0 q2
tof q1 q3 q0
tof q0 q2
tof q2 q3 q1
tof q3 q2
END
