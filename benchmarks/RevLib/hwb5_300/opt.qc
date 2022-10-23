# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/hwb5_300/circuit.qc):
#   Qubits: 28
#   H: 94
#   T: 329
#   X: 4
#   cnot: 319
#   Depth: 219
#   T depth: 98
# Result (2.373ms):
#   Qubits: 28
#   H: 94
#   T: 329
#   X: 4
#   cnot: 319
#   Depth: 219
#   T depth: 98
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27
BEGIN 
tof q4 q5
tof q0 q4 q5
tof q0 q5
tof q3 q6
tof q3 q5 q6
tof q5 q6
tof q0 q4 q7
tof q3 q8
tof q7 q8
tof q8
tof q1 q8 q6
tof q1 q6 q8
tof q4 q9
tof q0 q9
tof q3 q9 q10
tof q0 q4 q11
tof q4 q11
tof q11 q12
tof q3 q9 q12
tof q3 q11 q12
tof q1 q13
tof q12 q13
tof q1 q10 q13
tof q1 q12 q13
tof q13 q8
tof q2 q8 q13
tof q3 q14
tof q3 q7 q14
tof q7 q14
tof q3 q15
tof q11 q15
tof q3 q5 q15
tof q3 q11 q15
tof q15 q16
tof q1 q14 q16
tof q1 q15 q16
tof q0 q17
tof q3 q4 q17
tof q0 q3 q17
tof q1 q18
tof q17 q18
tof q1 q12 q18
tof q1 q17 q18
tof q18
tof q2 q18 q16
tof q2 q16 q18
tof q17 q15
tof q1 q15 q17
tof q11 q19
tof q3 q4 q19
tof q3 q11 q19
tof q7 q20
tof q0 q3 q20
tof q3 q7 q20
tof q20 q21
tof q1 q19 q21
tof q1 q20 q21
tof q21 q17
tof q2 q17 q21
tof q9 q22
tof q0 q3 q22
tof q3 q9 q22
tof q22 q19
tof q1 q19 q22
tof q5 q23
tof q3 q11 q23
tof q3 q5 q23
tof q3 q7 q24
tof q24 q23
tof q1 q23 q24
tof q24 q22
tof q2 q22 q24
tof q3 q11 q25
tof q3 q25
tof q3 q9
tof q9
tof q9 q25
tof q1 q25 q9
tof q7 q26
tof q3 q5 q26
tof q3 q7 q26
tof q3 q5 q27
tof q3 q27
tof q27
tof q1 q27 q26
tof q1 q26 q27
tof q27 q9
tof q2 q9 q27
END
