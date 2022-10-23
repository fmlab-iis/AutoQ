# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/86/circuit.qc):
#   Qubits: 86
#   H: 135
#   S: 48
#   T: 131
#   X: 51
#   Y: 22
#   Z: 20
#   cnot: 122
#   cz: 29
#   Depth: 45
#   T depth: 17
# Result (4.411ms):
#   Qubits: 86
#   H: 135
#   S: 48
#   T: 131
#   X: 51
#   Y: 22
#   Z: 20
#   cnot: 122
#   cz: 29
#   Depth: 45
#   T depth: 17
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85
BEGIN 
Z q83 q4
tof q3 q28
Z q85
tof q47
H q78
S q78
H q78
Y q31
H q44
tof q8 q21
X q73
H q73
S q34
H q64
S q64
H q64
S q83
T q20
Y q0
H q62
tof q33
Z q24 q74
Z q65
S q41
tof q35 q64 q60
H q6
X q85
H q85
T q40
tof q48 q62
Y q11
Z q57
H q39
H q36
S q36
H q36
S q45
H q73
tof q58
H q41
H q69
S q69
H q69
T q26
tof q56 q4 q54
Y q4
Z q55
tof q22 q31 q37
H q83
T q56
tof q58
tof q43 q18
tof q30
Y q40
X q34
H q34
S q41
tof q50
H q1
Z q48 q16
tof q22
Y q70
T q9
Z q77 q6
Y q39
S q65
tof q77 q83
H q14
S q14
H q14
tof q61
H q17
S q17
H q17
Z q19 q40
tof q13 q41
X q62
H q62
T q43
tof q35 q27
H q44
Z q18
X q47
H q47
Z q76 q26
H q60
S q60
H q60
tof q38
S q76
S q60
X q20
H q20
X q47
H q47
Z q84 q80
H q60
S q19
Z q64 q38
Y q14
H q10
X q25
H q25
H q39
S q39
H q39
S q70
tof q51 q23 q1
Z q36
tof q40
S q38
X q23
H q23
Z q65 q84
Z q16 q17
X q80
H q80
H q38
S q38
H q38
tof q33 q41
Z q50
Y q11
Z q0
X q51
H q51
tof q18
X q51
H q51
Z q38 q14
S q31
Z q61 q10
S q64
Y q45
tof q12 q7
H q13
T q10
tof q83 q18
T q83
tof q12 q48
H q30
S q30
H q30
H q76
S q76
H q76
X q76
H q76
Z q31
Z q33
tof q23
H q63
T q20
T q46
tof q49 q59
Z q52
H q48
S q48
H q48
Y q31
Y q72
Z q85 q11
T q37
Z q73 q27
tof q18 q40 q23
tof q64 q84
X q20
H q20
S q74
Z q37 q29
T q3
Y q76
X q57
H q57
X q11
H q11
tof q49
X q46
H q46
Z q40 q32
Z q59 q22
H q14
S q14
H q14
S q43
Z q28 q29
H q38
Z q62 q76
T q8
X q34
H q34
Z q36
X q4
H q4
tof q41 q53 q42
H q73
S q73
H q73
H q25
S q25
H q25
X q47
H q47
Y q21
tof q69 q56
H q11
S q11
H q11
tof q41
tof q8 q10 q31
tof q18 q8 q80
tof q45 q78 q5
Y q33
tof q32 q18 q29
Y q44
H q60
H q37
tof q58
S q65
tof q76 q20 q17
Z q30 q48
Z q41 q57
tof q42
tof q23
Z q84 q48
tof q31 q67
Z q51
H q49
tof q6 q78
Z q57 q78
H q32
H q36
tof q59 q67
tof q10 q14
H q33
S q33
H q33
Y q61
T q1
T q11
H q82
H q20
S q20
H q20
S q1
Z q57 q0
H q16
S q16
H q16
Z q38
Z q81
H q77
S q77
H q77
Z q71 q50
S q73
Z q8 q21
tof q61 q70 q19
H q81
S q81
H q81
tof q23 q66
Z q63
S q11
tof q59 q57 q43
T q9
tof q18 q21
tof q55
tof q14 q10 q64
tof q10 q85
X q63
H q63
Y q21
tof q57 q36
Z q37
tof q81 q10 q75
X q70
H q70
H q65
Z q47 q46
Z q60
tof q79
tof q33
S q30
tof q5 q29
Z q68
Y q42
H q62
Z q82 q13
H q78
S q78
H q78
S q37
X q85
H q85
H q63
X q36
H q36
tof q22 q3
tof q8 q54
H q81
S q81
H q81
H q78
T q20
H q61
S q46
Z q1
tof q28
tof q1 q12 q21
X q10
H q10
Y q20
Z q11 q57
H q25
S q25
H q25
tof q45 q25
tof q19
H q11
X q14
H q14
T q23
X q48
H q48
Y q13
S q7
H q47
T q37
S q31
X q73
H q73
Y q34
tof q23
END
