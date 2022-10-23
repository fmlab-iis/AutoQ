# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/37/circuit.qc):
#   Qubits: 37
#   H: 47
#   S: 15
#   T: 66
#   X: 22
#   Y: 16
#   Z: 7
#   cnot: 66
#   cz: 7
#   Depth: 41
#   T depth: 13
# Result (2.212ms):
#   Qubits: 37
#   H: 47
#   S: 15
#   T: 66
#   X: 22
#   Y: 16
#   Z: 7
#   cnot: 66
#   cz: 7
#   Depth: 41
#   T depth: 13
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36
BEGIN 
tof q35 q21 q11
H q32
tof q2 q0 q19
Z q13 q15
Y q7
Y q7
Z q14
Z q11
tof q5 q1
tof q14 q12
tof q6 q26 q32
Y q2
Y q11
Z q11 q28
Y q26
tof q24 q3
S q15
X q29
H q29
H q10
T q13
S q27
T q0
tof q26 q13
X q32
H q32
H q17
tof q34
Y q21
X q1
H q1
X q35
H q35
tof q16
H q31
S q31
H q31
tof q16 q34
tof q17
tof q26 q30 q29
H q5
Y q7
Y q20
T q26
tof q10 q36
H q22
S q22
H q22
Z q1
tof q11
Z q29 q27
S q1
tof q31 q36 q11
S q21
H q13
S q13
H q13
S q25
tof q1 q35
Z q30
tof q13 q18 q2
S q18
Z q5 q20
H q20
S q20
H q20
Z q17 q35
H q6
T q13
S q34
tof q36 q32 q26
tof q36 q25
tof q34
Y q24
X q20
H q20
X q1
H q1
Z q2
tof q29
tof q13
tof q13 q30
Z q5
tof q11 q33
tof q24
T q29
H q34
S q34
H q34
Z q33 q22
X q30
H q30
tof q4 q30
T q3
Y q15
Y q11
Y q21
H q12
S q12
H q12
tof q11 q16
tof q4 q5
H q34
tof q21 q4 q27
Y q27
tof q19 q6
Y q12
tof q25
tof q28 q34
S q12
tof q35
tof q27 q10
T q1
H q3
T q32
Y q17
X q30
H q30
tof q29
H q27
S q27
H q27
X q10
H q10
Z q11 q0
tof q14 q19
T q26
T q33
H q30
tof q3 q18
tof q20
tof q18
Z q33
Y q21
END
