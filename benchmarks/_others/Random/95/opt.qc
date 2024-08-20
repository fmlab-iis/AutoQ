# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/95/circuit.qc):
#   Qubits: 95
#   H: 119
#   S: 46
#   T: 157
#   X: 50
#   Y: 25
#   Z: 36
#   cnot: 144
#   cz: 24
#   Depth: 44
#   T depth: 18
# Result (4.613ms):
#   Qubits: 95
#   H: 119
#   S: 46
#   T: 157
#   X: 50
#   Y: 25
#   Z: 36
#   cnot: 144
#   cz: 24
#   Depth: 44
#   T depth: 18
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85 q86 q87 q88 q89 q90 q91 q92 q93 q94
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85 q86 q87 q88 q89 q90 q91 q92 q93 q94
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85 q86 q87 q88 q89 q90 q91 q92 q93 q94
BEGIN 
Z q67
H q37
Y q23
Z q61 q41
Z q55
tof q36
tof q41 q61
Z q29
tof q55
Z q75
X q63
H q63
tof q34 q56
tof q57 q79
S q74
H q84
S q84
H q84
Z q53
tof q88 q19
S q50
tof q76
T q44
H q50
tof q49 q65
T q5
Z q3 q65
S q37
T q76
tof q7 q30
T q56
tof q87 q11 q28
H q31
S q31
H q31
Z q33 q5
Y q22
H q73
S q73
H q73
T q35
Y q39
X q29
H q29
Z q73 q91
Z q15
H q60
S q60
H q60
H q26
S q26
H q26
H q80
S q80
H q80
Z q14 q69
X q39
H q39
Z q24 q19
T q29
tof q7 q79 q54
X q16
H q16
Y q17
tof q9 q3
Z q5
X q76
H q76
H q46
H q50
S q50
H q50
Z q67
T q52
Z q29 q91
tof q53 q16
tof q83
tof q80 q64 q45
X q80
H q80
Z q75 q67
X q78
H q78
T q36
Z q11
T q13
tof q12
tof q62 q45 q9
tof q74
X q90
H q90
tof q18 q65 q20
S q47
Y q51
Z q63
tof q82 q36 q12
Z q66 q45
tof q74 q7 q42
Z q20
S q33
T q7
S q41
Z q28
X q25
H q25
S q91
Y q43
S q86
tof q43
tof q38
X q77
H q77
Z q47
tof q31
tof q35 q73 q92
tof q72
H q19
X q62
H q62
Z q86
T q33
S q83
Z q52
tof q5 q40
tof q48 q10
tof q29 q85 q21
tof q18 q52
T q50
H q90
S q90
H q90
T q8
Z q21 q84
S q79
H q71
S q71
H q71
tof q90 q59
tof q44 q87
H q84
tof q88 q0 q86
tof q82 q12
S q2
Z q88 q52
S q81
Y q6
tof q76 q87 q84
tof q65 q61
H q60
S q10
Z q15
Y q91
T q42
tof q74 q59
T q84
Z q77 q54
T q31
tof q30
H q55
S q55
H q55
H q64
S q64
H q64
Y q22
Z q15 q83
Y q72
tof q6 q79
H q55
tof q11 q0
H q82
S q45
X q15
H q15
T q30
H q55
H q87
Z q39
T q12
tof q44
Y q4
T q31
Z q41 q34
X q64
H q64
Z q34
X q87
H q87
T q59
H q49
tof q60
T q63
S q34
T q10
S q84
tof q90 q73
tof q30 q77
Z q59
tof q50 q93
S q19
tof q50
H q74
tof q52 q27 q9
Z q84
X q51
H q51
H q18
S q18
H q18
Z q18 q1
Y q51
T q61
Z q26
Y q39
Z q1 q86
H q17
S q17
H q17
tof q71
S q0
H q26
S q26
H q26
T q75
H q43
tof q17 q91
Y q35
tof q91 q36
X q44
H q44
X q45
H q45
Z q56
tof q15 q43
Z q6
tof q6
tof q3 q70
Z q51 q94
S q31
tof q8 q93
S q4
tof q78
S q65
tof q77 q14 q46
X q86
H q86
H q13
Y q44
S q10
T q6
T q74
X q28
H q28
tof q75 q88
tof q9 q1 q57
tof q2 q30 q34
H q0
X q71
H q71
Y q2
tof q6 q3
tof q9 q47 q14
T q23
H q34
S q34
H q34
H q1
Z q29
Z q52
X q80
H q80
tof q47
X q49
H q49
Y q71
Z q75
Z q22 q87
Y q21
Y q26
X q1
H q1
Z q46
Z q2
Z q49
tof q65 q13
T q41
tof q18 q26
tof q62 q66
H q35
S q35
H q35
X q21
H q21
Z q33 q10
tof q51 q5
tof q81
Z q84
Z q22 q83
Y q68
Y q63
tof q14
Z q45 q29
Z q59 q91
T q30
H q29
S q29
H q29
S q56
tof q74
tof q73 q28
Z q83
T q73
H q43
S q43
H q43
S q57
tof q68
Y q9
S q55
tof q93
tof q44
Z q78
Z q87
H q67
H q72
S q7
S q35
tof q12 q21
Z q86
Y q92
Z q50 q39
H q91
H q10
S q10
H q10
Z q58 q9
X q7
H q7
X q16
H q16
Y q56
tof q17 q86
Z q75
Z q43
tof q30 q56 q79
T q23
Y q35
tof q18 q89
tof q60 q2 q13
END
