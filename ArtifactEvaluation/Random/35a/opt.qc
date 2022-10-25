# Feynman -- quantum circuit toolkit
# Original (Random/35a/circuit.qc):
#   Qubits: 35
#   H: 64
#   S: 17
#   T: 85
#   X: 16
#   Y: 11
#   Z: 9
#   cnot: 65
#   cz: 8
#   Depth: 50
#   T depth: 22
# Result (2.412ms):
#   Qubits: 35
#   H: 64
#   S: 17
#   T: 85
#   X: 16
#   Y: 11
#   Z: 9
#   cnot: 65
#   cz: 8
#   Depth: 50
#   T depth: 22
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34
BEGIN 
X q21
H q21
T q30
T q1
X q13
H q13
Z q16
tof q27 q13 q5
tof q8 q13 q18
T q6
Z q21 q30
H q20
Z q12
T q25
T q17
H q27
S q27
H q27
Z q6
Y q12
tof q11
H q8
S q8
H q8
Y q20
Z q13 q25
S q26
T q0
H q0
S q0
H q0
Y q5
T q19
H q14
H q22
S q22
H q22
Z q30
tof q23 q6
Z q21
X q20
H q20
Y q11
H q18
H q28
S q28
H q28
T q33
H q11
H q12
H q31
Z q26 q32
tof q0
T q33
Z q8 q29
X q8
H q8
Z q14
Z q31
T q17
tof q17
Y q27
T q20
tof q10 q8 q33
H q7
S q7
H q7
T q23
X q4
H q4
S q11
H q19
S q19
H q19
Z q0
H q19
S q19
H q19
Z q2
H q16
H q10
H q17
S q22
T q15
tof q12 q2
X q10
H q10
Z q34 q17
Y q10
tof q23 q21 q13
Y q19
Y q32
tof q0 q14 q28
H q1
S q1
H q1
H q28
S q28
H q28
tof q13 q2 q21
H q14
tof q1 q2 q3
tof q19 q6
S q17
tof q9
X q14
H q14
S q33
X q9
H q9
Z q23 q1
Y q34
X q29
H q29
tof q8 q19
tof q6 q16
Y q30
tof q23 q33 q31
S q16
Z q1 q10
tof q8
tof q21
Z q25 q8
T q13
S q9
H q11
tof q28 q32 q0
T q3
Y q21
H q23
H q20
X q17
H q17
tof q3 q18 q24
H q3
END
