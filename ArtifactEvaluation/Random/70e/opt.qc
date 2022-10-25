# Feynman -- quantum circuit toolkit
# Original (Random/70e/circuit.qc):
#   Qubits: 70
#   H: 119
#   S: 39
#   T: 116
#   X: 48
#   Y: 23
#   Z: 24
#   cnot: 95
#   cz: 14
#   Depth: 37
#   T depth: 15
# Result (3.763ms):
#   Qubits: 70
#   H: 119
#   S: 39
#   T: 116
#   X: 48
#   Y: 23
#   Z: 24
#   cnot: 95
#   cz: 14
#   Depth: 37
#   T depth: 15
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69
BEGIN 
Z q63 q24
X q53
H q53
Y q47
tof q0
tof q41
H q9
S q9
H q9
S q21
S q49
H q37
S q37
H q37
Z q67
X q48
H q48
tof q12 q7
tof q38
T q46
S q69
H q66
X q34
H q34
tof q2
tof q60
T q44
T q11
Y q17
X q47
H q47
tof q65
S q52
H q59
S q59
H q59
H q60
S q60
H q60
Y q64
Z q44
Y q1
H q21
S q21
H q21
Z q11
T q45
S q58
Z q15
Z q32
tof q43 q62 q67
T q46
S q43
Z q41 q44
Z q31
tof q57
H q26
S q26
H q26
T q3
H q2
S q2
H q2
Z q23
tof q58
tof q0
S q64
T q69
T q30
tof q30 q4 q61
H q47
X q63
H q63
H q25
S q25
H q25
H q3
S q3
H q3
Y q39
T q64
Y q54
Y q56
T q9
H q69
Z q11
tof q67 q22
Z q39
Z q56
tof q28
H q33
S q26
Y q16
tof q0 q41
tof q42 q47 q6
X q56
H q56
tof q1 q7 q48
Z q29
H q5
S q5
H q5
Z q23
Z q19 q60
tof q63 q19
tof q39
Z q20 q36
tof q13 q36
H q58
S q58
H q58
H q56
H q2
S q2
H q2
H q10
X q4
H q4
H q15
S q15
H q15
tof q2
Z q13
tof q6
Y q28
Z q50 q47
X q19
H q19
tof q4
tof q36 q30 q33
Z q30
X q43
H q43
tof q56
Y q47
Z q43 q48
H q18
tof q61
X q31
H q31
H q18
S q18
H q18
T q46
tof q49 q43
H q60
X q26
H q26
tof q31
S q1
tof q56 q29
Y q26
tof q56
X q67
H q67
H q30
tof q5 q15 q33
H q45
tof q3
Z q13
S q26
Y q36
H q42
S q42
tof q59
X q42
H q42
X q12
H q12
Y q49
H q21
S q21
H q21
X q37
H q37
tof q60 q54 q9
Y q69
Y q69
Z q64
X q61
H q61
T q40
T q3
H q37
S q37
H q37
S q68
X q15
H q15
H q69
S q69
H q69
H q62
S q62
H q62
Y q50
Z q48
tof q19 q38 q1
Z q15 q13
tof q14 q28
tof q39 q19 q63
Z q59
Y q34
H q65
Z q6
H q38
tof q61 q42 q7
Z q68 q55
H q17
S q17
H q17
H q14
Y q50
H q47
S q47
H q47
T q67
Z q46 q16
Y q10
Y q33
X q43
H q43
X q31
H q31
Z q50 q12
tof q41 q54
X q37
H q37
H q14
S q14
H q14
tof q11
Z q5
tof q30 q44
X q37
H q37
X q32
H q32
X q58
H q58
S q36
Z q20
H q61
Z q67
Y q40
Y q4
T q5
H q60
Z q36 q40
T q28
H q46
S q46
H q46
X q32
H q32
tof q38 q3 q8
tof q3 q7
S q21
tof q8 q12 q17
S q65
Z q38 q11
Y q55
tof q13 q55 q11
tof q9 q39 q52
H q39
S q43
X q30
H q30
tof q25
H q12
Z q66 q39
Z q8
Z q47 q15
T q15
H q19
S q19
H q19
H q2
T q68
Z q51
X q64
H q64
END
