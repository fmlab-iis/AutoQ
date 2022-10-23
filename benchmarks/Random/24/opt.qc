# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/24/circuit.qc):
#   Qubits: 24
#   H: 38
#   S: 15
#   T: 68
#   X: 11
#   Y: 7
#   Z: 3
#   cnot: 55
#   cz: 7
#   Depth: 44
#   T depth: 19
# Result (1.614ms):
#   Qubits: 24
#   H: 38
#   S: 15
#   T: 68
#   X: 11
#   Y: 7
#   Z: 3
#   cnot: 55
#   cz: 7
#   Depth: 44
#   T depth: 19
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23
BEGIN 
tof q18 q23 q2
Z q16 q15
T q22
tof q19 q5
X q18
H q18
tof q15 q20 q8
Z q20
tof q7
Y q6
H q18
S q18
H q18
H q14
S q14
H q14
Y q5
tof q10 q15 q1
S q22
tof q19
tof q15 q19
S q12
Y q17
T q16
X q4
H q4
T q1
tof q5 q12 q16
Y q22
T q2
S q22
tof q19 q13 q22
H q3
S q3
H q3
Z q18 q15
Z q5
Y q12
tof q23
Z q13
H q4
S q4
H q4
tof q14 q22
H q2
T q20
S q8
S q9
tof q12
tof q3 q10 q19
Z q2 q13
H q18
S q18
H q18
X q20
H q20
T q8
T q6
Z q0 q10
T q15
tof q1 q9 q8
tof q10
Y q5
H q6
S q6
H q6
H q0
tof q19 q8
X q1
H q1
tof q8 q11 q10
X q19
H q19
tof q20 q9
H q6
S q6
H q6
Z q5 q7
S q15
T q1
X q15
H q15
S q20
T q7
S q15
T q8
T q17
tof q14 q1
Z q16 q15
tof q6 q3
Y q21
Z q11 q18
END
