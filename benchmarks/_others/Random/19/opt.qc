# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/19/circuit.qc):
#   Qubits: 19
#   H: 36
#   S: 14
#   T: 27
#   X: 14
#   Y: 4
#   Z: 3
#   cnot: 22
#   cz: 4
#   Depth: 33
#   T depth: 12
# Result (2.011ms):
#   Qubits: 19
#   H: 36
#   S: 14
#   T: 27
#   X: 14
#   Y: 4
#   Z: 3
#   cnot: 22
#   cz: 4
#   Depth: 33
#   T depth: 12
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
BEGIN 
X q12
H q12
H q4
tof q15
S q11
X q11
H q11
tof q9
Z q1 q2
X q16
H q16
Z q13
H q8
S q8
H q8
T q12
X q4
H q4
S q0
H q0
S q0
H q0
tof q16
Y q6
tof q5 q3
X q14
H q14
Y q10
X q8
H q8
H q10
S q10
H q10
S q8
X q15
H q15
S q15
T q16
tof q9 q17 q2
tof q18 q0
H q15
S q15
H q15
X q10
H q10
Z q6 q15
H q5
H q5
H q1
T q1
H q0
tof q16 q15 q9
tof q14
tof q16 q4 q1
Z q14 q0
S q14
H q16
S q16
H q16
S q13
H q2
S q2
H q2
H q8
S q8
H q8
Z q3
tof q10
Y q3
Z q14
T q13
Y q18
tof q3 q18
T q4
T q11
H q16
S q16
H q16
tof q11 q10
X q16
H q16
Z q8 q15
END
