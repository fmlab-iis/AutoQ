# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/40/circuit.qc):
#   Qubits: 40
#   H: 46
#   S: 20
#   T: 75
#   X: 27
#   Y: 14
#   Z: 9
#   cnot: 65
#   cz: 12
#   Depth: 47
#   T depth: 18
# Result (2.599ms):
#   Qubits: 40
#   H: 46
#   S: 20
#   T: 75
#   X: 27
#   Y: 14
#   Z: 9
#   cnot: 65
#   cz: 12
#   Depth: 47
#   T depth: 18
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39
BEGIN 
tof q3 q25 q15
Z q17
tof q5 q21
X q39
H q39
tof q3 q11
tof q8 q24
T q13
Y q37
Y q30
Z q36 q27
S q9
S q2
Y q29
tof q19
tof q14 q28
T q12
tof q12 q11
T q15
H q4
S q4
H q4
tof q39
T q28
Z q38 q28
Y q20
Y q38
Z q25 q31
Z q19
tof q7
tof q16 q21
H q3
Z q19
Z q36
T q15
X q20
H q20
Y q2
Z q3 q23
X q31
H q31
tof q39 q7 q25
tof q32 q8
tof q3
tof q7
tof q28
S q3
H q6
S q6
H q6
Y q31
X q38
H q38
Z q37 q19
tof q39 q32 q17
T q11
Z q1
tof q16 q18 q32
H q18
S q18
H q18
H q4
H q39
tof q18 q12
X q33
H q33
Y q8
tof q4
tof q16
Y q9
S q33
tof q7 q0 q4
S q33
T q33
Z q31 q26
Y q23
Z q11 q15
S q21
Z q30
Z q37
tof q31 q33
tof q39 q35
S q29
S q39
Y q13
tof q5 q6 q34
tof q17 q25 q16
tof q9
tof q33
Y q3
tof q3
T q12
S q23
Y q25
Z q3 q13
tof q25
Z q25
Z q39
tof q19
H q16
S q16
H q16
T q14
Z q18 q4
S q9
T q18
X q35
H q35
H q38
S q38
H q38
T q5
tof q3
tof q10
tof q28
X q24
H q24
tof q29
H q5
Z q17 q2
H q19
tof q20 q38 q12
S q39
X q1
H q1
Y q28
T q3
S q12
tof q39 q27
S q38
Z q15 q22
X q4
H q4
Z q26 q7
H q28
S q28
H q28
H q1
tof q7 q31 q0
X q30
H q30
S q23
END
