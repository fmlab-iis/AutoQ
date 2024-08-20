# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/41/circuit.qc):
#   Qubits: 41
#   H: 74
#   S: 25
#   T: 78
#   X: 29
#   Y: 9
#   Z: 9
#   cnot: 67
#   cz: 13
#   Depth: 40
#   T depth: 11
# Result (2.743ms):
#   Qubits: 41
#   H: 74
#   S: 25
#   T: 78
#   X: 29
#   Y: 9
#   Z: 9
#   cnot: 67
#   cz: 13
#   Depth: 40
#   T depth: 11
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40
BEGIN 
Z q7
H q1
S q1
H q1
H q28
S q28
H q28
X q18
H q18
X q1
H q1
Z q18 q13
H q32
S q32
H q32
tof q27
Z q21 q39
Z q24 q7
X q17
H q17
tof q9 q28
Z q3 q30
tof q12
Z q13 q14
H q11
Z q24 q14
X q1
H q1
T q30
Z q32
Z q31
S q17
tof q37 q24
S q15
X q10
H q10
T q32
H q33
S q33
H q33
H q30
S q20
Z q8
S q38
H q4
S q4
H q4
H q37
S q37
H q37
X q31
H q31
tof q26 q8 q24
S q27
S q37
H q6
S q6
H q6
H q33
H q14
T q34
H q31
H q17
tof q28 q27
tof q25 q20 q8
Z q16 q2
T q8
X q26
H q26
tof q28 q15 q39
Z q28 q4
Z q20
tof q11
tof q16
tof q38 q39 q7
Y q25
tof q13
tof q19
Z q24
X q20
H q20
H q10
H q26
S q26
H q26
tof q22
Z q24
tof q29 q19
Y q11
X q38
H q38
H q14
T q27
tof q3
Z q39 q14
tof q4
T q31
H q17
S q17
H q17
T q19
H q20
tof q30 q1
tof q13
tof q21 q35 q3
H q27
tof q20
Z q36
H q14
tof q22 q12 q15
Z q16
Z q1 q3
tof q14 q24 q20
T q31
H q35
H q25
S q25
H q25
X q3
H q3
H q13
S q5
H q20
S q20
H q20
tof q11 q28 q21
tof q11 q33
Y q22
Z q1 q26
Y q32
H q39
S q39
H q39
tof q35 q29
tof q31
tof q5 q0 q18
S q13
S q33
tof q36
tof q40
Y q22
X q37
H q37
Z q3 q20
X q4
H q4
tof q0
tof q6 q40 q9
S q30
H q34
S q34
H q34
X q40
H q40
Y q23
Y q8
Y q20
H q37
S q37
H q37
Y q36
tof q3
Z q18 q22
S q38
END
