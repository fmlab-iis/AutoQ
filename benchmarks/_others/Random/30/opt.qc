# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/30/circuit.qc):
#   Qubits: 30
#   H: 48
#   S: 14
#   T: 63
#   X: 18
#   Y: 6
#   Z: 10
#   cnot: 57
#   cz: 10
#   Depth: 35
#   T depth: 15
# Result (2.203ms):
#   Qubits: 30
#   H: 48
#   S: 14
#   T: 63
#   X: 18
#   Y: 6
#   Z: 10
#   cnot: 57
#   cz: 10
#   Depth: 35
#   T depth: 15
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29
BEGIN 
Z q1 q7
X q29
H q29
Z q19 q29
tof q7 q3
tof q5 q2 q18
Z q10
Z q4 q19
Z q16
Z q29 q6
tof q18 q28 q27
tof q7
tof q2
tof q19
H q23
S q23
H q23
H q1
S q1
H q1
tof q17
S q11
Z q29
Z q10
tof q18
Z q13 q14
Y q0
tof q29 q4 q24
X q1
H q1
H q19
S q19
H q19
tof q14 q1
tof q15 q17
Y q16
X q21
H q21
Y q21
tof q3 q5 q7
tof q23 q13
tof q0 q27 q24
Z q26
T q21
H q29
Z q27
Y q17
H q6
Y q7
H q2
S q2
H q2
S q1
tof q23 q28 q2
tof q5
S q22
T q23
tof q7 q17
tof q26 q15 q25
tof q6
tof q1 q10
Z q21
Z q9 q21
S q11
Z q19 q17
T q9
T q22
Z q2
Z q16 q25
H q15
S q15
H q15
S q23
H q19
Z q7 q17
H q8
S q8
H q8
H q23
tof q5
X q13
H q13
H q27
Y q26
X q29
H q29
Z q18
tof q3
X q19
H q19
Z q16 q1
H q21
T q0
H q5
H q20
S q20
H q20
tof q16 q9
Z q0
H q1
S q1
H q1
H q22
T q19
T q6
tof q16 q24 q23
tof q15 q4
S q24
tof q28 q15
tof q29
X q26
H q26
X q29
H q29
END
