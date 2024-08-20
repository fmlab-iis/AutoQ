# Feynman -- quantum circuit toolkit
# Original (./29/circuit.qc):
#   Qubits: 30
#   H: 60
#   Z: 1
#   cnot: 15
#   Depth: 18
#   T depth: 0
# Result (2.077ms):
#   Qubits: 30
#   H: 60
#   Z: 1
#   cnot: 15
#   Depth: 18
#   T depth: 0
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29
BEGIN 
H q0
H q1
H q2
H q3
H q4
H q5
H q6
H q7
H q8
H q9
H q10
H q11
H q12
H q13
H q14
H q15
H q16
H q17
H q18
H q19
H q20
H q21
H q22
H q23
H q24
H q25
H q26
H q27
H q28
H q29
Z q29
tof q0 q29
tof q2 q29
tof q4 q29
tof q6 q29
tof q8 q29
tof q10 q29
tof q12 q29
tof q14 q29
tof q16 q29
tof q18 q29
tof q20 q29
tof q22 q29
tof q24 q29
tof q26 q29
tof q28 q29
H q0
H q1
H q2
H q3
H q4
H q5
H q6
H q7
H q8
H q9
H q10
H q11
H q12
H q13
H q14
H q15
H q16
H q17
H q18
H q19
H q20
H q21
H q22
H q23
H q24
H q25
H q26
H q27
H q28
H q29
END
