# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/82/circuit.qc):
#   Qubits: 82
#   H: 130
#   S: 35
#   T: 195
#   X: 52
#   Y: 26
#   Z: 17
#   cnot: 173
#   cz: 18
#   Depth: 50
#   T depth: 21
# Result (3.117ms):
#   Qubits: 82
#   H: 130
#   S: 35
#   T: 195
#   X: 52
#   Y: 26
#   Z: 17
#   cnot: 173
#   cz: 18
#   Depth: 50
#   T depth: 21
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81
BEGIN 
X q2
H q2
Z q19 q63
tof q64
X q30
H q30
S q59
H q3
H q71
S q71
H q71
X q57
H q57
tof q1
T q53
T q24
T q31
tof q64 q23
X q59
H q59
T q14
H q71
S q71
H q71
X q46
H q46
Z q18
T q44
tof q43 q16 q4
Z q8 q1
Y q57
T q42
H q47
X q10
H q10
tof q59 q76
S q55
S q68
tof q39 q59 q23
H q73
S q73
H q73
tof q68
T q45
T q54
tof q16
tof q55 q63 q40
tof q23
tof q26 q9 q80
S q68
tof q46
tof q51
H q32
S q32
H q32
tof q11 q58 q12
T q20
T q41
Y q29
tof q37
tof q0 q12 q31
T q72
tof q28 q18
tof q29 q43 q51
X q7
H q7
Y q73
Z q44 q81
Z q20
Y q59
tof q14 q20
tof q46 q38 q65
tof q38 q78 q43
Z q70
T q28
tof q0 q57
S q53
H q60
Z q74
T q29
H q78
S q78
H q78
H q8
Z q10 q22
tof q38 q68 q36
T q0
tof q22 q45
tof q12 q64
tof q20 q64
X q72
H q72
tof q81
tof q20
tof q74 q50
H q70
Z q78
H q34
S q34
H q34
tof q45 q73
X q1
H q1
Y q11
Z q39 q57
H q53
S q53
H q53
T q16
X q24
H q24
Z q63 q61
H q34
S q34
H q34
tof q13
H q54
H q16
S q16
H q16
Y q81
S q28
tof q29 q21 q31
tof q38
tof q30 q79
H q23
Y q61
T q42
tof q59 q25 q66
tof q61 q68
tof q5
tof q16 q23
X q17
H q17
tof q65 q39
X q4
H q4
Z q72 q45
T q20
T q54
H q13
S q13
H q13
S q5
H q38
Z q0
tof q66
Z q11
tof q69 q54
tof q13
tof q34 q22 q73
tof q62 q80 q66
X q43
H q43
H q77
tof q73 q41 q20
H q48
X q67
H q67
T q80
tof q19
X q22
H q22
Z q51 q76
Z q66 q4
H q8
H q66
S q66
H q66
Z q78
Y q45
tof q71
Z q46 q62
H q67
H q49
X q77
H q77
tof q64 q5 q22
S q29
tof q18 q23
T q2
tof q71 q13
Y q57
tof q24 q25 q50
T q14
T q29
Z q9
Z q8
tof q1
Z q62 q67
T q4
tof q38 q47 q50
H q48
S q48
H q48
Y q14
Y q67
Z q15
X q66
H q66
tof q41 q49 q57
X q80
H q80
tof q61 q15 q64
Z q18
Y q20
H q79
S q79
H q79
H q35
tof q74 q5
Y q40
tof q35 q79 q47
S q12
tof q61
Z q0 q30
H q52
S q52
H q52
X q6
H q6
tof q44
X q74
H q74
Y q58
Z q67 q57
Y q23
H q31
S q31
H q31
tof q36 q71
T q72
Y q58
tof q3 q16 q51
tof q18 q81
Y q72
tof q16 q24 q74
Y q16
tof q65
tof q44 q41
tof q67 q56
tof q15
H q11
T q2
Z q2
Z q5 q20
X q66
H q66
H q42
X q31
H q31
tof q11 q55 q65
Z q73
tof q3 q22
Y q46
H q71
tof q31 q6
Y q44
tof q37
Z q36
S q52
S q72
tof q16 q33
S q47
tof q43 q23
S q63
H q49
S q38
tof q35
Y q44
Y q2
Y q11
T q1
tof q11 q38
tof q63
H q70
S q70
H q70
X q31
H q31
Z q49 q78
H q11
S q11
H q11
X q57
H q57
Z q36 q24
tof q76
Z q19 q45
Y q77
Y q11
T q13
S q56
Y q53
Z q5 q68
tof q24 q19
H q74
S q74
H q74
Z q38
H q39
S q39
H q39
X q1
H q1
tof q39 q67
S q37
X q36
H q36
Z q1
END
