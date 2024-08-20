# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/23/circuit.qc):
#   Qubits: 23
#   H: 44
#   S: 13
#   T: 76
#   X: 9
#   Y: 7
#   Z: 5
#   cnot: 68
#   cz: 4
#   Depth: 49
#   T depth: 21
# Result (1.960ms):
#   Qubits: 23
#   H: 44
#   S: 13
#   T: 76
#   X: 9
#   Y: 7
#   Z: 5
#   cnot: 68
#   cz: 4
#   Depth: 49
#   T depth: 21
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22
BEGIN 
S q3
Z q6 q3
tof q13 q0
tof q20 q7
Y q10
tof q9 q8 q13
tof q6 q8
Y q12
T q20
H q0
S q0
H q0
H q16
Z q1 q21
Y q21
Z q3
Z q19
H q2
T q8
tof q2
H q0
S q20
X q3
H q3
T q16
tof q10
T q3
Y q21
tof q7 q16 q22
tof q13 q14 q16
Y q10
X q5
H q5
H q19
S q19
H q19
tof q10 q22 q20
S q4
H q13
tof q9 q0
tof q13 q4
S q10
tof q22 q11 q12
tof q10 q20 q6
H q8
Z q16
S q18
tof q20 q5 q6
tof q10
Z q6
X q18
H q18
tof q1 q10
tof q22 q5
X q12
H q12
Z q15 q18
H q19
S q19
H q19
tof q13
H q0
S q0
H q0
X q11
H q11
S q19
H q22
tof q1 q10
Z q5
H q7
S q7
H q7
H q20
S q20
H q20
T q5
tof q18 q10 q7
T q10
tof q15 q6 q12
H q1
Z q7 q12
Y q3
Y q1
tof q2 q5 q6
S q16
END
