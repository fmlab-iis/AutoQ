# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/ham7_299/circuit.qc):
#   Qubits: 21
#   H: 40
#   T: 140
#   X: 10
#   cnot: 151
#   Depth: 149
#   T depth: 58
# Result (2.298ms):
#   Qubits: 21
#   H: 40
#   T: 140
#   X: 10
#   cnot: 151
#   Depth: 149
#   T depth: 58
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
BEGIN 
tof q4 q7
tof q1 q7
tof q5 q8
tof q1 q8
tof q5 q7 q8
tof q1 q5 q8
tof q6 q9
tof q1 q9
tof q6 q8 q9
tof q1 q6 q9
tof q2 q9
tof q9
tof q0 q9
tof q9
tof q1 q10
tof q5 q7 q10
tof q1 q5 q10
tof q1 q11
tof q6 q10 q11
tof q1 q6 q11
tof q3 q11
tof q11
tof q2 q11
tof q11
tof q5 q12
tof q7 q12
tof q1 q5 q12
tof q5 q7 q12
tof q1 q13
tof q6 q12 q13
tof q1 q6 q13
tof q3 q13
tof q13
tof q0 q13
tof q13
tof q5 q14
tof q4 q5 q14
tof q4 q14
tof q6 q14 q15
tof q6 q15
tof q0 q15
tof q15
tof q6 q16
tof q8 q16
tof q1 q6 q16
tof q6 q8 q16
tof q4 q5 q17
tof q5 q17
tof q6 q18
tof q6 q17 q18
tof q17 q18
tof q2 q18
tof q18
tof q4 q5 q19
tof q4 q19
tof q6 q20
tof q6 q19 q20
tof q19 q20
tof q3 q20
tof q20
tof q9
END
