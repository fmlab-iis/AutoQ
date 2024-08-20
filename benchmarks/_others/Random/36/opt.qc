# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/36/circuit.qc):
#   Qubits: 36
#   H: 67
#   S: 21
#   T: 84
#   X: 21
#   Y: 6
#   Z: 8
#   cnot: 78
#   cz: 11
#   Depth: 33
#   T depth: 11
# Result (2.566ms):
#   Qubits: 36
#   H: 67
#   S: 21
#   T: 84
#   X: 21
#   Y: 6
#   Z: 8
#   cnot: 78
#   cz: 11
#   Depth: 33
#   T depth: 11
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35
BEGIN 
H q26
S q26
H q26
T q9
Y q14
S q28
Z q4 q11
tof q24 q16
H q23
S q23
H q23
X q35
H q35
tof q18
T q13
H q30
X q30
H q30
H q27
X q15
H q15
Z q22 q5
H q32
X q24
H q24
Z q12
T q13
X q18
H q18
Z q19
X q20
H q20
tof q19
X q5
H q5
H q34
S q34
H q34
S q6
S q34
tof q0
Z q12 q9
tof q17 q19
H q17
S q17
H q17
T q25
tof q11 q18
S q29
tof q11 q29
S q18
H q20
S q20
H q20
Y q5
H q7
S q7
H q7
tof q28 q22
tof q8 q3
H q33
Y q33
tof q19 q14
tof q24
Z q16 q6
tof q26
H q27
tof q0 q25 q8
H q28
S q28
H q28
Z q20
X q5
H q5
Z q21 q29
H q5
tof q34 q8
Y q31
tof q6 q16
H q9
S q9
H q9
Z q19
Z q2 q20
X q18
H q18
X q1
H q1
tof q22 q29 q4
tof q8 q9 q14
tof q2
Z q15 q12
tof q23 q4 q19
Z q26
tof q8
tof q28 q7 q20
tof q27 q16 q28
S q17
H q14
S q14
H q14
S q3
Y q35
S q30
tof q10
S q24
H q13
S q13
H q13
tof q7 q13
tof q33
tof q27 q12
Z q34 q13
Z q25 q29
Z q18
tof q18 q32
tof q21 q33 q32
H q27
tof q4 q32 q25
H q26
Z q30 q19
X q7
H q7
tof q27 q19 q28
H q12
S q12
H q12
T q30
Z q2
X q13
H q13
H q9
T q22
Z q3 q16
tof q24 q0 q26
T q23
Y q11
tof q31 q11 q24
Z q2
H q30
S q0
H q1
END
