# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/34/circuit.qc):
#   Qubits: 34
#   H: 52
#   S: 16
#   T: 61
#   X: 24
#   Y: 10
#   Z: 11
#   cnot: 58
#   cz: 10
#   Depth: 31
#   T depth: 12
# Result (1.772ms):
#   Qubits: 34
#   H: 52
#   S: 16
#   T: 61
#   X: 24
#   Y: 10
#   Z: 11
#   cnot: 58
#   cz: 10
#   Depth: 31
#   T depth: 12
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33
BEGIN 
Z q1
T q17
S q10
Z q24
H q27
Z q0
X q31
H q31
tof q13
tof q33 q10
tof q20
Z q10
Z q7
X q28
H q28
H q14
T q4
tof q11 q21 q6
Y q31
tof q13
Y q21
tof q17
H q9
S q9
H q9
tof q30
tof q30 q6
H q16
S q16
H q16
S q12
tof q18 q1
Z q17
Z q2
X q12
H q12
Y q16
tof q2 q22 q13
tof q5
X q27
H q27
Z q17
tof q11 q13 q28
H q20
S q20
H q20
Y q32
tof q16
tof q30 q25 q29
tof q15
S q8
H q11
S q11
H q11
Z q20 q13
X q33
H q33
X q26
H q26
Z q4 q15
tof q23 q1 q4
tof q16 q32
Z q14 q3
tof q18 q33
tof q13 q0 q11
Y q2
Y q20
S q9
S q29
H q0
H q33
S q33
H q33
tof q1 q22 q32
X q14
H q14
Z q12
Z q3 q15
S q29
X q8
H q8
tof q2 q8 q28
tof q18
H q26
S q26
H q26
tof q15 q33
T q2
tof q20
Z q5 q21
H q3
X q12
H q12
H q14
S q14
H q14
tof q4
H q19
H q26
S q26
H q26
T q24
Z q9 q26
tof q28 q24
S q8
tof q33 q26
Y q15
Y q25
Y q15
Z q31
Z q8 q32
tof q31 q2
tof q24
T q9
tof q8
X q0
H q0
tof q19 q28
H q19
Z q31 q27
Z q13
H q31
Z q2 q12
tof q33
Z q17 q31
H q22
S q22
H q22
H q25
Y q25
END
