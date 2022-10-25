# Feynman -- quantum circuit toolkit
# Original (Random/70i/circuit.qc):
#   Qubits: 70
#   H: 122
#   S: 37
#   T: 176
#   X: 43
#   Y: 24
#   Z: 17
#   cnot: 153
#   cz: 19
#   Depth: 40
#   T depth: 15
# Result (3.576ms):
#   Qubits: 70
#   H: 122
#   S: 37
#   T: 176
#   X: 43
#   Y: 24
#   Z: 17
#   cnot: 153
#   cz: 19
#   Depth: 40
#   T depth: 15
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69
BEGIN 
T q61
X q31
H q31
Z q41
tof q54
Z q55
T q36
T q16
tof q61 q59 q9
H q22
S q22
H q22
T q68
H q0
tof q21 q54 q60
tof q1
tof q14 q4 q0
X q15
H q15
T q54
X q25
H q25
S q52
tof q41 q68 q57
Y q0
X q56
H q56
tof q56 q54
Z q68 q5
Y q53
S q3
Z q18 q30
tof q30 q18 q16
Z q14 q27
Y q65
tof q43 q36
X q30
H q30
T q44
H q54
tof q24
H q46
S q46
H q46
tof q68 q58
H q6
Z q14 q36
H q14
Z q64
tof q10 q8
S q50
T q33
tof q51 q7 q53
Y q51
X q45
H q45
tof q46 q37 q48
H q47
S q47
H q47
T q29
tof q40
H q31
S q31
H q31
S q69
tof q10
Z q38 q18
Z q18
H q41
S q41
H q41
H q14
S q14
H q14
tof q48 q5
S q0
tof q32 q58 q30
tof q69 q19
Y q28
Y q53
Z q46
X q12
H q12
Z q10 q66
H q41
S q41
H q41
tof q15
tof q46 q69
tof q37
tof q48 q9
Z q41
H q47
Y q6
X q32
H q32
tof q4 q47 q3
H q24
Z q42 q40
tof q38
T q66
T q41
tof q31
S q56
tof q41
tof q31 q17
Z q8
H q34
S q34
H q34
H q63
S q63
H q63
tof q1
Y q56
Z q18 q59
tof q1
tof q53 q26 q23
X q9
H q9
tof q11 q3 q22
tof q45 q69 q53
S q16
tof q26 q47 q44
S q52
Y q37
Y q26
tof q65 q16
tof q66 q43
tof q34 q66 q59
H q45
S q45
H q45
S q59
Z q22
tof q8 q17
Y q37
tof q21
H q14
S q14
H q14
S q8
tof q11
X q10
H q10
Z q61 q38
S q69
Z q55 q46
H q44
S q44
H q44
Y q65
tof q45
S q20
T q25
H q16
tof q7 q37 q30
Y q12
tof q5
tof q46 q15 q57
H q54
S q54
H q54
Z q61
X q18
H q18
Y q27
Z q23
Z q61
tof q39 q11 q33
Y q61
H q10
S q10
H q10
Z q17 q52
tof q41 q32 q24
H q20
S q20
H q20
X q63
H q63
Y q23
X q4
H q4
tof q57
X q0
H q0
Y q19
tof q65 q30 q4
X q63
H q63
H q9
S q44
Y q1
S q38
Z q0 q62
T q32
Z q54
Z q9
H q61
H q11
S q53
H q5
Y q22
tof q34 q40
H q68
S q68
H q68
H q25
T q11
tof q10
Y q69
tof q54 q60 q28
Z q41 q50
tof q32
S q9
Y q27
H q36
H q58
tof q21
X q66
H q66
tof q32 q21 q3
Z q48
Z q36 q47
H q20
S q20
H q20
Z q32
H q23
T q41
tof q48
H q42
S q42
H q42
Y q43
H q45
H q8
tof q64 q61 q68
X q35
H q35
H q29
S q29
H q29
Y q67
H q57
S q57
H q57
Z q20 q8
tof q64
Z q1
Z q40 q22
Z q67 q7
tof q40 q27
tof q13 q48 q43
X q39
H q39
tof q32
Y q3
Z q26 q12
T q25
tof q8
Z q46
Z q44 q59
X q26
H q26
tof q11 q24
S q19
END
