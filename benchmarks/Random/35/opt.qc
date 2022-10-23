# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/35/circuit.qc):
#   Qubits: 35
#   H: 58
#   S: 18
#   T: 78
#   X: 16
#   Y: 8
#   Z: 11
#   cnot: 74
#   cz: 8
#   Depth: 45
#   T depth: 18
# Result (2.500ms):
#   Qubits: 35
#   H: 58
#   S: 18
#   T: 78
#   X: 16
#   Y: 8
#   Z: 11
#   cnot: 74
#   cz: 8
#   Depth: 45
#   T depth: 18
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34
BEGIN 
H q31
T q3
H q25
S q25
H q25
Z q32
H q28
Z q15
H q17
S q17
H q17
tof q2
H q21
Z q11 q32
S q5
tof q33
tof q27 q3
Z q10
H q24
S q24
H q24
H q10
S q10
H q10
Y q12
Z q8 q21
tof q13
T q2
H q16
Z q27
tof q22 q13
Y q19
Z q34 q26
S q3
tof q17 q23 q5
X q24
H q24
tof q14 q29 q13
Z q14
tof q14
T q34
Y q18
tof q29
T q33
tof q0
tof q13 q16
tof q17
Z q29
tof q13 q17
Z q30
S q30
H q1
X q13
H q13
T q8
T q21
Y q33
H q23
tof q15 q21
tof q28 q13
Z q9
tof q17 q5 q34
H q31
S q31
H q31
H q24
S q24
H q24
Z q12 q32
tof q14 q5 q3
tof q25 q19 q5
Z q17 q33
X q10
H q10
Y q31
tof q6 q22
tof q16 q26
H q33
S q33
H q33
tof q20 q29
S q21
tof q8 q18
H q34
S q34
H q34
S q14
H q26
H q23
S q23
H q23
X q16
H q16
H q23
tof q12
H q11
tof q18 q8 q11
X q33
H q33
Y q12
tof q16 q20
S q26
tof q23 q25
Y q24
tof q24
T q2
Z q6
S q11
S q33
X q25
H q25
Z q18 q21
Z q30
T q28
H q32
H q21
S q21
H q21
H q29
tof q24 q29 q14
tof q31 q18 q30
Z q33
H q7
tof q31 q1
tof q31
tof q26 q14 q1
Z q9 q3
tof q7 q4
Y q25
Z q2 q26
tof q29 q32 q13
END
