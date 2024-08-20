# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/bw_291/circuit.qc):
#   Qubits: 87
#   H: 318
#   T: 1113
#   X: 34
#   cnot: 1068
#   Depth: 777
#   T depth: 342
# Result (5.025ms):
#   Qubits: 87
#   H: 318
#   T: 1113
#   X: 34
#   cnot: 1068
#   Depth: 777
#   T depth: 342
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85 q86
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85 q86
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85 q86
BEGIN 
tof q2 q4 q5
tof q4 q5
tof q5 q6
tof q1 q2 q6
tof q1 q5 q6
tof q2 q7
tof q3 q6 q7
tof q2 q3 q7
tof q2 q4 q8
tof q4 q9
tof q2 q9
tof q1 q10
tof q1 q9 q10
tof q9 q10
tof q3 q11
tof q10 q11
tof q3 q8 q11
tof q3 q10 q11
tof q11 q12
tof q0 q7 q12
tof q0 q11 q12
tof q1 q2 q13
tof q1 q13
tof q1 q8 q14
tof q1 q14
tof q3 q15
tof q1 q15
tof q3 q14 q15
tof q1 q3 q15
tof q15 q16
tof q0 q13 q16
tof q0 q15 q16
tof q4 q17
tof q2 q4 q17
tof q2 q17
tof q17 q18
tof q1 q4 q18
tof q1 q17 q18
tof q3 q19
tof q14 q19
tof q3 q18 q19
tof q3 q14 q19
tof q19 q20
tof q0 q2 q20
tof q0 q19 q20
tof q3 q21
tof q17 q21
tof q3 q8 q21
tof q3 q17 q21
tof q21 q22
tof q0 q2 q22
tof q0 q21 q22
tof q2 q23
tof q1 q17 q23
tof q1 q2 q23
tof q3 q23 q24
tof q3 q24
tof q2 q4 q25
tof q2 q25
tof q25 q26
tof q1 q8 q26
tof q1 q25 q26
tof q3 q27
tof q26 q27
tof q3 q10 q27
tof q3 q26 q27
tof q27 q24
tof q0 q24 q27
tof q1 q28
tof q1 q5 q28
tof q5 q28
tof q3 q29
tof q28 q29
tof q3 q8 q29
tof q3 q28 q29
tof q29 q30
tof q0 q2 q30
tof q0 q29 q30
tof q6 q31
tof q2 q3 q31
tof q3 q6 q31
tof q25 q32
tof q1 q9 q32
tof q1 q25 q32
tof q9 q33
tof q1 q2 q33
tof q1 q9 q33
tof q33
tof q3 q33 q32
tof q3 q32 q33
tof q33 q34
tof q0 q31 q34
tof q0 q33 q34
tof q2 q35
tof q1 q5 q35
tof q1 q2 q35
tof q35 q36
tof q3 q23 q36
tof q3 q35 q36
tof q8 q37
tof q1 q9 q37
tof q1 q8 q37
tof q3 q37 q38
tof q38 q36
tof q0 q36 q38
tof q1 q9 q39
tof q1 q39
tof q3 q40
tof q39 q40
tof q3 q17 q40
tof q3 q39 q40
tof q40 q31
tof q0 q31 q40
tof q1 q8 q41
tof q8 q41
tof q3 q42
tof q41 q42
tof q3 q8 q42
tof q3 q41 q42
tof q42 q43
tof q0 q2 q43
tof q0 q42 q43
tof q3 q44
tof q3 q5 q44
tof q5 q44
tof q3 q45
tof q37 q45
tof q45 q46
tof q0 q44 q46
tof q0 q45 q46
tof q17 q47
tof q1 q2 q47
tof q1 q17 q47
tof q47 q48
tof q3 q6 q48
tof q3 q47 q48
tof q2 q49
tof q1 q8 q49
tof q1 q2 q49
tof q1 q4 q50
tof q4 q50
tof q3 q51
tof q50 q51
tof q3 q49 q51
tof q3 q50 q51
tof q51 q48
tof q0 q48 q51
tof q1 q8 q52
tof q52 q53
tof q3 q8 q53
tof q3 q52 q53
tof q53 q54
tof q0 q2 q54
tof q0 q53 q54
tof q5 q55
tof q3 q6 q55
tof q3 q5 q55
tof q5 q56
tof q1 q9 q56
tof q1 q5 q56
tof q3 q56 q57
tof q56 q57
tof q57 q55
tof q0 q55 q57
tof q5 q58
tof q1 q17 q58
tof q1 q5 q58
tof q58 q59
tof q3 q47 q59
tof q3 q58 q59
tof q3 q8 q60
tof q60 q61
tof q0 q59 q61
tof q0 q60 q61
tof q9 q62
tof q1 q25 q62
tof q1 q9 q62
tof q3 q63
tof q62 q63
tof q3 q37 q63
tof q3 q62 q63
tof q0 q64
tof q0 q63 q64
tof q63 q64
tof q3 q49 q65
tof q65 q66
tof q0 q2 q66
tof q0 q65 q66
tof q17 q67
tof q1 q5 q67
tof q1 q17 q67
tof q67 q68
tof q3 q5 q68
tof q3 q67 q68
tof q25
tof q3 q25 q23
tof q3 q23 q25
tof q25 q69
tof q0 q68 q69
tof q0 q25 q69
tof q2 q70
tof q3 q13 q70
tof q2 q3 q70
tof q17 q71
tof q1 q8 q71
tof q1 q17 q71
tof q1 q72
tof q1 q17 q72
tof q17 q72
tof q3 q73
tof q72 q73
tof q3 q71 q73
tof q3 q72 q73
tof q73 q70
tof q0 q70 q73
tof q1 q17 q74
tof q1 q74
tof q3 q75
tof q74 q75
tof q3 q8 q75
tof q3 q74 q75
tof q75 q76
tof q0 q2 q76
tof q0 q75 q76
tof q2 q77
tof q3 q35 q77
tof q2 q3 q77
tof q3 q78
tof q39 q78
tof q3 q8 q78
tof q3 q39 q78
tof q78 q77
tof q0 q77 q78
tof q9 q79
tof q1 q5 q79
tof q1 q9 q79
tof q10
tof q3 q10 q79
tof q3 q79 q10
tof q0 q80
tof q0 q10 q80
tof q10 q80
tof q3 q81
tof q9 q81
tof q3 q37 q81
tof q3 q9 q81
tof q81 q44
tof q0 q44 q81
tof q3 q67 q82
tof q3 q82
tof q9 q83
tof q1 q17 q83
tof q1 q9 q83
tof q14
tof q3 q14 q83
tof q3 q83 q14
tof q14 q82
tof q0 q82 q14
tof q60 q7
tof q0 q7 q60
tof q58
tof q3 q58 q62
tof q3 q62 q58
tof q58 q68
tof q0 q68 q58
tof q9 q8
tof q1 q8 q9
tof q17
tof q3 q17 q9
tof q3 q9 q17
tof q17 q84
tof q0 q2 q84
tof q0 q17 q84
tof q3 q85
tof q3 q72 q85
tof q72 q85
tof q0 q86
tof q0 q85 q86
tof q85 q86
tof q12
tof q16
tof q20
tof q22
tof q27
tof q30
tof q34
tof q38
tof q40
tof q43
tof q46
tof q51
tof q54
tof q57
tof q61
tof q64
tof q66
tof q69
tof q73
tof q76
tof q78
tof q80
tof q81
tof q14
tof q60
tof q58
tof q84
tof q86
END
