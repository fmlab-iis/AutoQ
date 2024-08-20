# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Random/20/circuit.qc):
#   Qubits: 20
#   H: 34
#   S: 12
#   T: 32
#   X: 16
#   Y: 5
#   Z: 5
#   cnot: 28
#   cz: 5
#   Depth: 34
#   T depth: 12
# Result (1.960ms):
#   Qubits: 20
#   H: 34
#   S: 12
#   T: 32
#   X: 16
#   Y: 5
#   Z: 5
#   cnot: 28
#   cz: 5
#   Depth: 34
#   T depth: 12
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
BEGIN 
Z q19
tof q3 q18
H q19
S q19
H q19
H q13
S q13
H q13
T q8
H q4
S q4
H q4
H q6
S q6
H q6
H q18
Z q15 q0
Z q12
Y q14
Y q5
S q12
H q12
tof q19
X q3
H q3
tof q1
Y q2
tof q19 q14 q4
H q10
S q14
tof q17
Z q0
S q12
Z q16
tof q10
tof q15 q18 q7
Z q17 q10
S q0
Z q1 q3
tof q12 q9
H q0
S q0
H q0
Y q3
H q4
S q4
H q4
tof q6
Z q3
X q9
H q9
X q10
H q10
H q4
S q4
H q4
tof q6
tof q5 q19
tof q7
tof q4
tof q1
T q11
S q8
H q14
tof q3 q1
X q8
H q8
T q19
Y q18
tof q14 q0 q18
X q18
H q18
Z q3 q18
X q10
H q10
H q19
X q6
H q6
T q5
tof q18 q13 q6
Z q8 q7
END
