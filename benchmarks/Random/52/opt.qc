# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/52/circuit.qc):
#   Qubits: 52
#   H: 85
#   S: 42
#   T: 120
#   X: 23
#   Y: 9
#   Z: 14
#   cnot: 102
#   cz: 15
#   Depth: 39
#   T depth: 16
# Result (3.332ms):
#   Qubits: 52
#   H: 85
#   S: 42
#   T: 120
#   X: 23
#   Y: 9
#   Z: 14
#   cnot: 102
#   cz: 15
#   Depth: 39
#   T depth: 16
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51
BEGIN 
tof q21
Z q33 q39
H q27
S q40
Z q25 q11
S q38
tof q4
tof q21
tof q40 q2 q15
tof q21 q51 q43
Y q49
H q7
H q30
S q30
H q30
H q17
Z q19 q22
tof q44 q38
S q45
H q35
tof q4 q39
tof q1 q43
S q32
S q31
Z q34 q50
Z q31 q42
tof q50
Z q14
S q37
H q38
S q38
H q38
H q30
S q30
H q30
T q35
tof q50 q18
T q30
Z q44 q32
tof q17 q12 q8
H q13
S q13
H q13
Z q23
Z q21
Z q25
H q39
T q35
S q0
H q0
S q0
H q0
tof q22
tof q30 q20
S q13
tof q40
Z q31
tof q51 q19 q21
tof q8 q11 q24
S q9
H q49
T q1
Y q40
Z q12 q38
H q19
S q19
H q19
H q41
T q4
H q38
S q38
H q38
H q35
S q35
H q35
tof q10 q48
tof q29
T q44
T q33
tof q38
tof q6 q35
tof q7
Z q12
S q11
Z q14
H q34
S q34
H q34
S q31
Z q26 q18
H q9
Z q4
H q6
S q6
H q6
Z q3 q51
Y q37
tof q10
Z q50
tof q51
tof q44 q11
Z q31
Y q32
S q19
S q17
Z q37 q35
tof q22 q32 q31
T q42
T q3
S q20
S q0
tof q21 q22 q30
tof q9 q48 q44
X q28
H q28
tof q13
X q24
H q24
H q28
S q28
H q28
H q50
tof q5 q30
S q10
S q41
tof q38
H q12
S q12
H q12
X q8
H q8
tof q35 q7
tof q24 q16 q36
tof q11
H q23
S q23
H q23
H q4
tof q23 q33 q7
S q7
T q28
H q50
S q50
H q50
H q2
S q2
H q2
Y q15
H q0
S q0
H q0
Z q48 q10
Z q3
Z q14
Z q10 q7
H q51
tof q35
Z q30 q34
T q37
T q48
S q9
T q24
Z q40
S q1
Y q16
tof q0 q26 q49
tof q0 q11
H q39
S q39
H q39
tof q9 q38 q0
S q18
tof q30 q7 q43
tof q32
Y q48
tof q17
Z q6 q33
tof q10 q49 q19
Z q0
Y q41
tof q3 q44 q15
H q29
S q29
H q29
tof q25 q48
Y q3
tof q23
H q12
S q12
H q12
tof q38
H q9
S q9
H q9
Z q12 q42
X q23
H q23
S q3
T q16
T q27
END
