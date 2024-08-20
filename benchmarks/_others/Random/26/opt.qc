# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/26/circuit.qc):
#   Qubits: 26
#   H: 51
#   S: 21
#   T: 75
#   X: 10
#   Y: 10
#   Z: 5
#   cnot: 66
#   cz: 4
#   Depth: 43
#   T depth: 17
# Result (2.194ms):
#   Qubits: 26
#   H: 51
#   S: 21
#   T: 75
#   X: 10
#   Y: 10
#   Z: 5
#   cnot: 66
#   cz: 4
#   Depth: 43
#   T depth: 17
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25
BEGIN 
Z q14
tof q7 q5
tof q16 q22 q13
H q9
H q20
S q20
H q20
S q24
Y q21
Y q11
H q15
tof q11 q24 q18
H q17
Y q20
H q11
S q11
H q11
X q6
H q6
H q14
S q14
H q14
tof q11
tof q20 q24 q5
tof q20 q19
X q25
H q25
H q7
S q6
S q4
T q24
H q4
S q4
H q4
H q5
S q5
H q5
Y q4
H q9
S q9
H q9
Y q10
Z q8
X q3
H q3
S q21
Y q11
H q24
S q24
H q24
S q0
S q23
tof q13 q3 q9
tof q23 q7 q17
T q24
tof q3 q16
S q16
H q14
H q24
H q7
S q7
H q7
X q23
H q23
tof q7 q23
Z q9
tof q22 q20
S q1
tof q5 q0 q12
T q3
S q23
H q16
S q16
H q16
S q24
tof q17
Y q8
S q4
X q13
H q13
tof q10
Y q3
T q8
Z q9
Y q16
Z q10
T q13
Y q20
Z q12 q18
S q2
tof q23
tof q25 q10 q22
Z q16 q14
tof q22 q24
Z q0 q11
Z q4 q20
tof q20 q6 q5
X q19
H q19
tof q14 q12 q16
tof q13 q20 q16
H q8
END
