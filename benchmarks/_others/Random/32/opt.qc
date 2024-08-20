# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/32/circuit.qc):
#   Qubits: 32
#   H: 48
#   S: 17
#   T: 57
#   X: 21
#   Y: 6
#   Z: 11
#   cnot: 51
#   cz: 11
#   Depth: 32
#   T depth: 12
# Result (2.356ms):
#   Qubits: 32
#   H: 48
#   S: 17
#   T: 57
#   X: 21
#   Y: 6
#   Z: 11
#   cnot: 51
#   cz: 11
#   Depth: 32
#   T depth: 12
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31
BEGIN 
X q2
H q2
tof q5
Y q31
Z q21
Z q30 q22
X q6
H q6
T q24
Z q14 q17
tof q22
S q22
H q28
tof q18 q25 q0
Z q30 q14
T q0
H q23
H q9
S q9
H q9
tof q29 q12
tof q16 q18
Z q8
tof q5 q25
X q27
H q27
X q3
H q3
S q0
H q21
S q21
H q21
S q4
S q24
tof q6 q24
tof q29
tof q6 q11 q30
Z q23 q18
Z q9 q8
tof q2
H q21
S q21
H q21
S q8
Z q18 q12
X q23
H q23
T q20
tof q21 q12
S q27
H q10
tof q4 q16
X q2
H q2
X q26
H q26
T q7
Z q29 q3
H q10
S q10
H q10
H q21
S q21
H q21
T q17
H q31
S q31
H q31
Z q30 q0
X q26
H q26
H q11
S q11
H q11
Z q16 q15
tof q9
tof q3 q12
Z q23
Z q11 q30
X q8
H q8
tof q17 q18
Y q6
Y q11
H q4
tof q12
Z q22
T q26
tof q14 q11 q17
H q20
Z q3
X q27
H q27
S q7
H q25
S q25
H q25
tof q14 q26 q3
tof q20
T q6
Y q23
T q21
Z q16 q11
H q10
X q23
H q23
Y q30
X q9
H q9
Y q27
S q30
tof q17
tof q14 q4
tof q9
Z q20
Z q17
Z q28
S q6
Z q11
tof q29 q20 q0
Z q11
tof q8 q2 q31
Z q29
tof q9 q19 q27
END
