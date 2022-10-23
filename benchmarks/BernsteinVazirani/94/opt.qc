# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/BernsteinVazirani/94/circuit.qc):
#   Qubits: 95
#   H: 189
#   Z: 1
#   cnot: 47
#   Depth: 50
#   T depth: 0
# Result (1.670ms):
#   Qubits: 95
#   H: 189
#   Z: 1
#   cnot: 47
#   Depth: 50
#   T depth: 0
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85 q86 q87 q88 q89 q90 q91 q92 q93 q94
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85 q86 q87 q88 q89 q90 q91 q92 q93 q94
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85 q86 q87 q88 q89 q90 q91 q92 q93 q94
BEGIN 
H q0
H q1
H q2
H q3
H q4
H q5
H q6
H q7
H q8
H q9
H q10
H q11
H q12
H q13
H q14
H q15
H q16
H q17
H q18
H q19
H q20
H q21
H q22
H q23
H q24
H q25
H q26
H q27
H q28
H q29
H q30
H q31
H q32
H q33
H q34
H q35
H q36
H q37
H q38
H q39
H q40
H q41
H q42
H q43
H q44
H q45
H q46
H q47
H q48
H q49
H q50
H q51
H q52
H q53
H q54
H q55
H q56
H q57
H q58
H q59
H q60
H q61
H q62
H q63
H q64
H q65
H q66
H q67
H q68
H q69
H q70
H q71
H q72
H q73
H q74
H q75
H q76
H q77
H q78
H q79
H q80
H q81
H q82
H q83
H q84
H q85
H q86
H q87
H q88
H q89
H q90
H q91
H q92
H q93
H q94
Z q94
tof q0 q94
tof q2 q94
tof q4 q94
tof q6 q94
tof q8 q94
tof q10 q94
tof q12 q94
tof q14 q94
tof q16 q94
tof q18 q94
tof q20 q94
tof q22 q94
tof q24 q94
tof q26 q94
tof q28 q94
tof q30 q94
tof q32 q94
tof q34 q94
tof q36 q94
tof q38 q94
tof q40 q94
tof q42 q94
tof q44 q94
tof q46 q94
tof q48 q94
tof q50 q94
tof q52 q94
tof q54 q94
tof q56 q94
tof q58 q94
tof q60 q94
tof q62 q94
tof q64 q94
tof q66 q94
tof q68 q94
tof q70 q94
tof q72 q94
tof q74 q94
tof q76 q94
tof q78 q94
tof q80 q94
tof q82 q94
tof q84 q94
tof q86 q94
tof q88 q94
tof q90 q94
tof q92 q94
H q0
H q1
H q2
H q3
H q4
H q5
H q6
H q7
H q8
H q9
H q10
H q11
H q12
H q13
H q14
H q15
H q16
H q17
H q18
H q19
H q20
H q21
H q22
H q23
H q24
H q25
H q26
H q27
H q28
H q29
H q30
H q31
H q32
H q33
H q34
H q35
H q36
H q37
H q38
H q39
H q40
H q41
H q42
H q43
H q44
H q45
H q46
H q47
H q48
H q49
H q50
H q51
H q52
H q53
H q54
H q55
H q56
H q57
H q58
H q59
H q60
H q61
H q62
H q63
H q64
H q65
H q66
H q67
H q68
H q69
H q70
H q71
H q72
H q73
H q74
H q75
H q76
H q77
H q78
H q79
H q80
H q81
H q82
H q83
H q84
H q85
H q86
H q87
H q88
H q89
H q90
H q91
H q92
H q93
END
