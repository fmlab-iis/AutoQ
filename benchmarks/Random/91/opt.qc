# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/91/circuit.qc):
#   Qubits: 91
#   H: 137
#   S: 47
#   T: 193
#   X: 42
#   Y: 33
#   Z: 27
#   cnot: 167
#   cz: 19
#   Depth: 44
#   T depth: 18
# Result (4.387ms):
#   Qubits: 91
#   H: 137
#   S: 47
#   T: 193
#   X: 42
#   Y: 33
#   Z: 27
#   cnot: 167
#   cz: 19
#   Depth: 44
#   T depth: 18
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85 q86 q87 q88 q89 q90
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85 q86 q87 q88 q89 q90
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85 q86 q87 q88 q89 q90
BEGIN 
S q35
H q23
Z q46
H q9
tof q79 q81 q51
tof q83
tof q35
X q2
H q2
Z q62
tof q72
Z q49
Z q9
H q29
H q63
S q8
Z q0
Y q23
Z q72
Y q30
Y q22
Y q19
T q20
S q82
Z q46 q16
tof q27 q77
S q68
tof q27 q6
tof q53
Z q22 q24
S q17
S q52
tof q42 q45
tof q27 q90 q4
X q73
H q73
Y q13
S q68
Z q76
tof q70
T q73
X q80
H q80
Z q80
X q31
H q31
tof q83 q74 q2
Z q7 q81
tof q35
tof q51
Y q25
Z q71 q46
Y q9
H q18
X q84
H q84
X q71
H q71
S q43
tof q42 q74
tof q88 q20
Y q0
H q14
S q14
H q14
X q8
H q8
tof q5 q14 q21
H q39
H q6
S q70
H q81
S q81
H q81
S q21
tof q15
S q37
H q42
S q42
H q42
Z q4
H q39
S q39
H q39
H q10
S q10
H q10
Y q43
T q10
Z q85 q69
H q69
S q69
H q69
X q31
H q31
Y q10
Y q69
Y q33
tof q64 q34
H q28
S q28
H q28
tof q67 q33
tof q34 q36 q24
T q46
H q28
S q28
H q28
tof q37 q5 q28
S q88
tof q74
H q5
H q72
S q72
H q72
H q36
X q67
H q67
T q12
T q55
X q52
H q52
H q31
Y q34
tof q71 q43
Y q8
Z q82
Z q15 q61
H q22
T q57
H q0
T q65
S q71
H q63
tof q63
H q55
S q55
H q55
Z q25 q86
Z q22 q13
Z q65
H q80
S q80
H q80
H q50
S q50
H q50
tof q30 q20
Z q52 q64
Y q42
Z q17 q16
Z q51
Z q0
H q84
H q24
T q16
S q72
tof q49
H q66
tof q41 q81 q68
tof q74 q88
T q35
tof q34 q41 q53
Y q20
tof q65 q78
S q34
H q72
S q72
H q72
Z q70
T q3
Y q35
tof q66 q65 q33
T q18
Z q41
tof q61 q23 q0
Z q57 q41
S q71
T q1
H q12
S q79
H q27
S q27
H q27
Y q80
S q66
T q23
T q33
Y q78
S q70
Z q17
S q21
tof q72 q71 q7
X q82
H q82
tof q48 q47 q87
Y q2
tof q71
Z q48
Y q71
H q81
Y q32
S q55
tof q90 q34
tof q70 q15 q54
Z q51 q34
X q74
H q74
tof q33 q85
tof q29 q17 q1
Z q88
T q26
Z q28 q67
H q32
Z q14 q50
S q13
S q23
H q26
tof q67 q77 q21
X q23
H q23
Z q54
T q9
Z q35
Z q61
H q20
T q33
Z q26
Z q43
H q75
S q75
H q75
H q24
S q24
H q24
tof q14
Z q7 q40
tof q74 q81
Z q4
Y q44
T q85
H q13
Y q43
tof q41 q64 q87
Z q75
tof q45 q28 q19
Y q85
tof q44
tof q16
H q65
X q88
H q88
tof q84 q55 q86
Y q76
H q17
S q17
H q17
H q35
S q35
H q35
tof q36 q39
S q33
X q72
H q72
H q32
tof q38 q25
Z q44 q32
Z q61 q84
X q37
H q37
S q38
X q9
H q9
H q85
tof q76
tof q47
Y q90
tof q60 q87
Y q46
tof q61 q78 q58
tof q66
S q16
Z q33 q40
tof q53 q77 q8
tof q33 q71 q88
Z q83
tof q57 q2 q56
H q80
H q1
T q46
X q77
H q77
tof q88 q52
tof q13
tof q88
tof q78 q13
T q50
S q90
tof q27
tof q76 q64 q47
Z q30 q12
Y q19
tof q2 q17
tof q28 q3
H q79
S q79
H q79
T q68
S q42
H q72
Y q41
T q80
H q37
tof q62
H q59
H q37
Y q28
T q47
tof q39
Z q27
tof q3 q85
Y q83
tof q28 q48
tof q56
T q48
H q67
tof q4 q67 q74
H q57
Y q64
END
