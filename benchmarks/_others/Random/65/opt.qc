# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/65/circuit.qc):
#   Qubits: 65
#   H: 98
#   S: 37
#   T: 115
#   X: 36
#   Y: 20
#   Z: 23
#   cnot: 106
#   cz: 13
#   Depth: 37
#   T depth: 15
# Result (3.539ms):
#   Qubits: 65
#   H: 98
#   S: 37
#   T: 115
#   X: 36
#   Y: 20
#   Z: 23
#   cnot: 106
#   cz: 13
#   Depth: 37
#   T depth: 15
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64
BEGIN 
Y q19
H q50
tof q46
S q3
S q50
Z q60
Y q21
X q23
H q23
X q49
H q49
Y q49
H q48
H q4
S q4
H q4
H q58
S q58
H q58
tof q39 q2
H q3
S q3
H q3
T q51
Z q59
S q42
tof q47
X q51
H q51
H q39
S q39
H q39
tof q16 q0
Z q0
tof q9
tof q9 q64
S q37
Z q32
Y q34
tof q42
S q58
Y q28
X q63
H q63
tof q52 q45 q34
T q25
Y q47
H q10
S q43
Z q18 q32
T q18
tof q22 q12
X q36
H q36
tof q29 q13 q21
tof q44 q51 q11
T q56
tof q24 q25
Z q51
Z q24 q29
H q31
S q31
H q31
T q21
X q42
H q42
X q7
H q7
H q27
S q27
H q27
tof q61 q0
tof q27 q14
tof q51 q60 q14
tof q37 q7
H q61
X q41
H q41
tof q6 q0
S q54
Z q26
Y q23
T q15
tof q9 q44
T q8
X q58
H q58
X q61
H q61
tof q22 q56 q37
H q30
S q30
H q30
Z q24
H q13
S q13
H q13
Z q13
Z q3
H q11
S q11
H q11
Z q56 q22
T q62
H q29
S q29
H q29
tof q19 q17
Z q1 q11
S q62
Y q9
Z q7
tof q20 q53
S q49
Z q60
S q24
Y q27
Z q39
tof q60
Z q18
H q4
S q4
H q4
H q56
H q41
X q34
H q34
S q55
X q39
H q39
tof q13 q9 q3
S q1
T q7
tof q52 q31 q63
T q4
tof q37 q1
tof q57 q36 q16
S q27
Y q62
S q9
tof q15 q3
tof q28
H q1
S q1
H q1
Z q15
tof q39 q14
H q8
tof q63
Z q52 q36
T q1
tof q53 q18 q49
Z q58
X q40
H q40
tof q8
tof q20 q11
H q50
S q50
H q50
tof q58
Z q41 q49
H q55
H q4
S q4
H q4
Y q30
Y q56
Y q35
S q33
tof q13
S q40
Z q1
X q12
H q12
Y q7
Y q25
tof q20 q51 q56
X q27
H q27
tof q37
X q9
H q9
Z q21
X q63
H q63
S q44
X q8
H q8
H q60
S q60
H q60
H q32
tof q31 q36
Z q45
tof q63 q15
H q62
T q59
tof q13 q23 q33
Y q42
T q29
tof q22 q30
Y q1
Y q26
Z q63
tof q50 q36 q17
T q26
X q6
H q6
Z q12 q16
Y q49
Y q14
tof q36 q49 q51
tof q30 q17
H q52
Z q33
T q52
Z q8 q50
H q60
S q60
H q60
X q64
H q64
Z q47 q61
tof q9
tof q42 q33
H q55
T q60
Z q36 q46
S q1
X q60
H q60
S q50
Z q46 q37
X q54
H q54
X q8
H q8
H q43
S q43
H q43
tof q2 q28 q5
Z q37
Z q6 q7
tof q61
T q7
Z q27
tof q3 q31
S q0
Z q42
Z q1 q17
H q58
END
