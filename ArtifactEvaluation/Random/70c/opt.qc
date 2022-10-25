# Feynman -- quantum circuit toolkit
# Original (Random/70c/circuit.qc):
#   Qubits: 70
#   H: 107
#   S: 35
#   T: 106
#   X: 38
#   Y: 23
#   Z: 23
#   cnot: 85
#   cz: 21
#   Depth: 34
#   T depth: 12
# Result (3.907ms):
#   Qubits: 70
#   H: 107
#   S: 35
#   T: 106
#   X: 38
#   Y: 23
#   Z: 23
#   cnot: 85
#   cz: 21
#   Depth: 34
#   T depth: 12
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69
BEGIN 
Y q1
tof q39
tof q3 q48
Z q69 q35
tof q39 q69 q23
Y q39
Z q64 q9
X q64
H q64
Z q46
H q21
S q21
H q21
X q56
H q56
tof q17
T q34
T q13
tof q21
H q56
S q56
H q56
Z q53 q67
S q16
Y q45
Z q28 q26
H q34
S q34
H q34
tof q54 q28 q43
T q16
Z q36 q2
Z q65 q14
Z q47 q27
X q69
H q69
Y q51
tof q10
H q57
S q57
H q57
S q27
T q19
T q1
H q31
S q31
H q31
H q12
S q12
H q12
H q21
S q21
H q21
Y q18
S q21
S q63
tof q46
X q6
H q6
Z q58 q17
tof q39
tof q64 q30
tof q32
tof q1
H q55
S q55
H q55
Z q33
tof q62
Z q42 q26
tof q2 q53 q63
X q47
H q47
tof q23 q52
Y q39
H q56
T q10
T q17
tof q52 q61 q40
Z q66 q25
tof q29
Z q14
tof q38
Z q46 q40
Z q51
H q12
H q41
Z q42 q22
Y q41
tof q0
H q4
S q4
H q4
Y q49
H q23
tof q3 q60
H q45
S q45
H q45
Y q22
tof q35 q62 q38
T q28
Z q35
tof q34 q6 q1
tof q40 q61
X q15
H q15
Z q69 q31
tof q60 q38
T q47
T q24
S q29
T q20
Y q69
H q0
H q65
S q65
H q65
Y q52
Y q66
tof q61
Y q41
Z q29
H q56
tof q30 q55
Z q69 q7
S q53
Z q6
tof q65
tof q32
X q64
H q64
tof q11
X q65
H q65
H q48
T q6
H q43
H q34
S q34
H q34
Z q47
Z q55
S q18
X q18
H q18
H q36
tof q69 q55
H q6
S q6
H q6
X q58
H q58
H q30
S q30
H q30
H q23
S q23
H q23
S q28
Z q9 q43
Z q61
S q25
X q31
H q31
Z q69
H q33
H q44
H q67
S q67
H q67
H q65
S q65
H q65
tof q7
tof q14 q43
H q26
Z q54
Z q34 q12
T q56
Z q54
X q14
H q14
tof q26
tof q35 q37 q15
Z q67 q59
Z q64
H q0
tof q31 q21
T q16
Y q54
Y q26
S q8
Z q64
Z q48 q61
H q4
Z q9
Z q60 q47
X q1
H q1
Y q7
H q50
T q64
S q61
Y q34
H q12
S q12
H q12
Z q52
tof q5
Y q31
Z q55
H q14
Y q25
X q2
H q2
Z q29 q61
T q42
T q65
H q39
Z q42
H q29
S q9
S q25
Y q43
H q56
tof q49
X q31
H q31
T q24
tof q38 q63 q25
S q34
T q55
T q5
Z q54
Z q31 q26
Y q2
H q40
H q6
tof q25 q24
Z q1
tof q17 q32 q4
X q56
H q56
tof q46 q23 q52
T q40
H q16
S q16
H q16
H q42
S q42
H q42
T q32
tof q38 q63
X q19
H q19
Y q12
H q67
X q49
H q49
tof q63 q53 q34
Z q69
Y q23
Z q63
tof q36 q3 q29
tof q19 q28
H q31
H q16
S q16
H q16
END
