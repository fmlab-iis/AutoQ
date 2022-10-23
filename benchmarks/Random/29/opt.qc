# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/29/circuit.qc):
#   Qubits: 29
#   H: 37
#   S: 16
#   T: 26
#   X: 15
#   Y: 8
#   Z: 11
#   cnot: 26
#   cz: 8
#   Depth: 25
#   T depth: 5
# Result (2.198ms):
#   Qubits: 29
#   H: 37
#   S: 16
#   T: 26
#   X: 15
#   Y: 8
#   Z: 11
#   cnot: 26
#   cz: 8
#   Depth: 25
#   T depth: 5
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28
BEGIN 
tof q22
tof q16 q4
Y q19
H q26
S q26
H q26
tof q23 q18
H q13
S q13
H q13
H q22
Y q23
H q2
X q17
H q17
tof q10 q15
tof q11 q3
X q16
H q16
H q18
Z q21 q5
Z q16 q22
Y q14
tof q24
H q22
T q18
H q0
Z q6
Y q15
Y q14
tof q4 q25 q26
S q12
tof q13 q2
Z q18
H q27
S q27
H q27
S q17
tof q13
T q8
H q18
S q18
H q18
Z q10 q17
H q14
tof q15
H q18
S q18
H q18
Y q16
S q6
Z q18
tof q12
T q2
S q2
T q18
H q5
tof q23 q5
Y q4
Z q3
tof q12 q20 q21
H q27
X q18
H q18
H q28
H q16
S q6
H q2
S q2
H q2
X q1
H q1
Z q21 q23
T q4
H q0
Z q4
tof q24
tof q25 q2
Z q16 q15
tof q14
Z q13
tof q26 q1
S q24
S q3
Z q19
S q26
H q20
Y q7
S q25
Z q15
Z q14
S q14
Z q2
Z q2
tof q7
tof q10 q16 q18
tof q20
Z q4 q15
Z q23 q12
X q18
H q18
X q16
H q16
H q14
Z q16 q22
END
