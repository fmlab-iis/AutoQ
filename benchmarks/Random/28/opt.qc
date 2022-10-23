# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/28/circuit.qc):
#   Qubits: 28
#   H: 54
#   S: 18
#   T: 95
#   X: 15
#   Y: 8
#   Z: 6
#   cnot: 76
#   cz: 6
#   Depth: 44
#   T depth: 16
# Result (2.206ms):
#   Qubits: 28
#   H: 54
#   S: 18
#   T: 95
#   X: 15
#   Y: 8
#   Z: 6
#   cnot: 76
#   cz: 6
#   Depth: 44
#   T depth: 16
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27
BEGIN 
tof q3
T q1
S q14
Y q25
H q6
S q6
H q6
tof q11 q18 q1
X q4
H q4
Y q16
T q19
tof q12 q26
Y q26
H q5
S q5
H q5
S q23
Z q12
H q9
S q9
H q9
tof q26 q0 q9
T q9
tof q6
Y q15
H q17
S q17
H q17
tof q1
S q4
tof q10 q26 q15
H q9
tof q27
tof q8 q6 q4
tof q4 q25 q27
Y q25
Z q2
Z q24
H q7
S q7
H q7
tof q5 q8
H q18
S q18
H q18
tof q0
T q21
T q25
Z q19 q22
H q18
Z q14 q22
X q18
H q18
S q6
T q13
H q19
S q19
H q19
H q22
S q22
H q22
S q11
H q18
T q2
tof q3 q2 q8
tof q11 q5 q16
tof q25
S q8
Z q12
H q14
S q14
H q14
X q21
H q21
X q2
H q2
H q22
X q25
H q25
tof q2 q0 q25
X q2
H q2
tof q9
S q19
tof q13 q2
Z q1
Z q3 q7
H q26
S q26
H q26
Z q27 q12
T q20
tof q6 q7 q22
Y q4
Z q15
tof q26 q21 q3
tof q14 q20 q7
S q5
Z q5 q7
T q20
Y q1
tof q2
tof q3 q7 q4
Y q13
T q24
tof q0 q25
tof q16
T q2
Z q23 q0
END
