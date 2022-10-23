# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/25/circuit.qc):
#   Qubits: 25
#   H: 45
#   S: 12
#   T: 58
#   X: 13
#   Y: 9
#   Z: 4
#   cnot: 59
#   cz: 4
#   Depth: 36
#   T depth: 12
# Result (1.856ms):
#   Qubits: 25
#   H: 45
#   S: 12
#   T: 58
#   X: 13
#   Y: 9
#   Z: 4
#   cnot: 59
#   cz: 4
#   Depth: 36
#   T depth: 12
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24
BEGIN 
Z q4
T q11
H q7
S q7
H q7
Y q1
tof q8
H q12
X q7
H q7
H q24
X q14
H q14
Y q23
tof q9 q1 q20
tof q19 q16 q6
H q6
tof q20 q1
H q3
tof q15 q7
tof q23 q20
H q5
H q16
tof q13
Z q15
tof q15 q18 q11
S q18
H q1
S q1
H q1
H q19
tof q1
tof q13
Z q22
S q0
S q6
tof q4 q1 q17
tof q24 q10
tof q14 q18
tof q5
Y q8
tof q6 q15 q21
tof q11 q8
X q3
H q3
Y q22
Y q19
Z q6 q0
Z q10 q3
X q21
H q21
H q5
tof q19 q21
tof q19
Y q5
H q21
H q20
S q20
H q20
H q20
S q20
H q20
tof q2 q8 q11
Y q5
Y q19
S q21
tof q7 q8
tof q3
tof q7
Y q3
S q7
H q0
S q0
H q0
X q2
H q2
tof q8 q15
T q2
Z q10
tof q21 q23 q4
H q12
H q8
Z q23 q17
tof q0 q21
H q8
S q8
H q8
tof q6 q12
H q3
Z q1 q8
S q9
tof q20 q14 q11
END
