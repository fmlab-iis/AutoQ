# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/MCToffoli/15/circuit.qc):
#   Qubits: 30
#   H: 56
#   T: 196
#   cnot: 169
#   Depth: 212
#   T depth: 86
# Result (0.967ms):
#   Qubits: 30
#   H: 56
#   T: 196
#   cnot: 169
#   Depth: 212
#   T depth: 86
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29
BEGIN 
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q11 q10 q12
tof q13 q12 q14
tof q15 q14 q16
tof q17 q16 q18
tof q19 q18 q20
tof q21 q20 q22
tof q23 q22 q24
tof q25 q24 q26
tof q27 q26 q28
tof q28 q29
tof q27 q26 q28
tof q25 q24 q26
tof q23 q22 q24
tof q21 q20 q22
tof q19 q18 q20
tof q17 q16 q18
tof q15 q14 q16
tof q13 q12 q14
tof q11 q10 q12
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
END
