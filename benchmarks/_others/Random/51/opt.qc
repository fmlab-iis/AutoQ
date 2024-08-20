# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/51/circuit.qc):
#   Qubits: 51
#   H: 84
#   S: 24
#   T: 132
#   X: 26
#   Y: 14
#   Z: 14
#   cnot: 113
#   cz: 16
#   Depth: 53
#   T depth: 21
# Result (3.035ms):
#   Qubits: 51
#   H: 84
#   S: 24
#   T: 132
#   X: 26
#   Y: 14
#   Z: 14
#   cnot: 113
#   cz: 16
#   Depth: 53
#   T depth: 21
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50
BEGIN 
tof q9 q14
S q17
tof q7
tof q19 q3 q5
tof q9 q15 q33
H q17
S q44
H q44
S q44
H q44
T q36
Z q29 q25
Z q26
tof q15 q33
H q49
tof q41 q16 q42
S q19
tof q0 q50 q15
T q39
Z q20
X q39
H q39
S q29
Z q46 q14
X q50
H q50
T q16
Y q32
Z q6 q5
H q27
S q27
H q27
tof q45
T q18
tof q28
tof q38
Z q28 q0
tof q22
Z q27
Z q8
H q6
S q0
X q36
H q36
T q29
tof q22 q9 q1
H q43
tof q3
T q34
tof q28 q21 q22
tof q46 q10
Z q0 q12
Z q8 q45
tof q5 q19 q47
S q10
tof q6 q8 q28
tof q44
X q3
H q3
H q30
tof q26 q32 q33
tof q37 q28
S q39
Z q45 q50
Y q13
H q41
S q41
H q41
tof q13
tof q17 q13 q36
H q21
X q5
H q5
Z q33 q8
Y q12
Z q11
Z q1 q7
tof q4 q14 q44
H q8
Z q42
S q9
H q28
S q28
H q28
S q11
Z q10
S q16
Y q10
Z q20 q43
Y q31
H q48
Y q24
T q23
X q27
H q27
Z q47 q8
Z q13 q24
tof q23
tof q18 q20
tof q37
Z q12 q28
tof q22 q23
tof q15 q27
X q20
H q20
tof q0 q18
Z q23
X q49
H q49
tof q17
tof q5 q30 q29
tof q27 q34
tof q47
H q50
tof q37 q1
S q9
Z q15
H q26
S q26
H q26
H q18
S q18
H q18
Y q24
T q45
H q31
Y q6
T q48
Y q27
H q31
S q31
H q31
S q35
X q25
H q25
Z q18
tof q21 q19 q10
Y q18
Z q28
tof q49
Y q17
X q5
H q5
H q43
H q29
tof q7 q1 q34
Z q2 q40
tof q11
Z q12
T q25
Y q42
Y q22
tof q37 q21 q23
X q44
H q44
H q22
H q22
S q22
H q22
Z q32 q38
Y q39
Z q39 q47
H q28
S q26
H q21
S q21
H q21
H q35
S q35
H q35
T q37
Z q29
H q41
Z q4
H q17
tof q17 q6 q18
tof q12 q24
T q17
tof q1 q31 q9
S q8
T q42
X q38
H q38
H q3
H q50
END
