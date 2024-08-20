# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/plus63mod4096_309/circuit.qc):
#   Qubits: 23
#   H: 20
#   T: 70
#   X: 17
#   cnot: 82
#   Depth: 80
#   T depth: 31
# Result (1.162ms):
#   Qubits: 23
#   H: 20
#   T: 70
#   X: 17
#   cnot: 82
#   Depth: 80
#   T depth: 31
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22
BEGIN 
tof q10 q12
tof q10 q11 q12
tof q11 q12
tof q9 q13
tof q9 q12 q13
tof q12 q13
tof q8 q14
tof q8 q13 q14
tof q13 q14
tof q7 q15
tof q7 q14 q15
tof q14 q15
tof q6 q16
tof q6 q15 q16
tof q15 q16
tof q5 q16 q17
tof q4 q17 q18
tof q3 q18 q19
tof q2 q19 q20
tof q1 q20 q21
tof q0 q21
tof q21
tof q1 q20
tof q20
tof q2 q19
tof q19
tof q3 q18
tof q18
tof q4 q17
tof q17
tof q5 q16
tof q16
tof q6 q15
tof q15
tof q7 q14
tof q14
tof q8 q13
tof q13
tof q9 q12
tof q12
tof q10 q22
tof q11 q22
tof q21
tof q20
tof q19
tof q18
tof q17
tof q16
tof q11
END
