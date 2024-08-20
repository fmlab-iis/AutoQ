# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/43/circuit.qc):
#   Qubits: 43
#   H: 59
#   S: 21
#   T: 106
#   X: 23
#   Y: 7
#   Z: 19
#   cnot: 88
#   cz: 11
#   Depth: 55
#   T depth: 23
# Result (1.405ms):
#   Qubits: 43
#   H: 59
#   S: 21
#   T: 106
#   X: 23
#   Y: 7
#   Z: 19
#   cnot: 88
#   cz: 11
#   Depth: 55
#   T depth: 23
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42
BEGIN 
Z q32
S q11
Z q3 q31
T q17
X q41
H q41
H q24
S q24
H q24
T q31
S q35
Z q31
X q36
H q36
Z q10
Z q35
tof q15
tof q10
Y q42
S q10
X q41
H q41
Z q35 q30
Z q1
T q8
Z q39
Z q3
H q25
S q25
H q25
tof q22 q30 q39
T q40
tof q7 q35 q5
X q2
H q2
S q9
tof q36
tof q23 q14
tof q10 q32
S q25
Z q42 q21
tof q2
S q39
tof q35 q18 q36
tof q8
H q13
S q13
H q13
tof q23
Y q3
Z q16
T q34
Z q8 q5
S q19
T q9
X q20
H q20
Z q15 q34
Z q27 q31
tof q11 q41
S q18
tof q10 q23 q7
H q39
S q39
H q39
T q31
Z q30
tof q19 q38 q28
tof q6
X q11
H q11
H q27
H q15
tof q41
tof q41 q32
H q40
Z q29
T q27
X q2
H q2
S q32
tof q41 q37
X q21
H q21
H q14
S q14
H q14
tof q7 q12 q5
tof q12 q24 q13
H q42
S q27
tof q1 q38
H q18
tof q17
tof q9 q12 q42
Z q3 q36
S q24
H q33
S q5
tof q19
X q15
H q15
tof q21
Z q42 q32
tof q24 q25
tof q3 q35 q13
tof q30 q23
Z q42 q22
T q2
S q1
tof q5
T q32
H q37
tof q18 q1 q8
T q0
Y q21
S q16
S q16
tof q31 q30 q25
T q10
H q9
X q24
H q24
tof q31 q26 q22
H q9
Z q39
Y q12
Z q39
tof q3 q40
Z q16 q0
H q12
S q12
H q12
Y q41
tof q38 q23
Z q5
Z q27 q21
H q31
X q22
H q22
Z q3
Y q7
Z q27
Y q6
tof q32 q2 q12
T q18
Z q16
T q21
Z q22
Z q30
Z q14
T q9
END
