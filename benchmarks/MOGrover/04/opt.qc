# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/MOGrover/4/circuit.qc):
#   Qubits: 12
#   H: 89
#   T: 210
#   X: 25
#   cnot: 207
#   cz: 3
#   Depth: 256
#   T depth: 102
# Result (2.879ms):
#   Qubits: 12
#   H: 89
#   T: 210
#   X: 25
#   cnot: 207
#   cz: 3
#   Depth: 256
#   T depth: 102
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
BEGIN 
tof q11
H q4
H q5
H q7
H q9
H q11
tof q0 q4
tof q1 q5
tof q2 q7
tof q3 q9
tof q4 q5 q6
tof q7 q6 q8
tof q9 q8 q10
tof q10 q11
tof q9 q8 q10
tof q7 q6 q8
tof q4 q5 q6
tof q0 q4
tof q1 q5
tof q2 q7
tof q3 q9
H q4
H q5
H q7
H q9
tof q4
tof q5
tof q7
tof q9
tof q4 q5 q6
tof q7 q6 q8
Z q8 q9
tof q7 q6 q8
tof q4 q5 q6
tof q4
tof q5
tof q7
tof q9
H q4
H q5
H q7
H q9
tof q0 q4
tof q1 q5
tof q2 q7
tof q3 q9
tof q4 q5 q6
tof q7 q6 q8
tof q9 q8 q10
tof q10 q11
tof q9 q8 q10
tof q7 q6 q8
tof q4 q5 q6
tof q0 q4
tof q1 q5
tof q2 q7
tof q3 q9
H q4
H q5
H q7
H q9
tof q4
tof q5
tof q7
tof q9
tof q4 q5 q6
tof q7 q6 q8
Z q8 q9
tof q7 q6 q8
tof q4 q5 q6
tof q4
tof q5
tof q7
tof q9
H q4
H q5
H q7
H q9
tof q0 q4
tof q1 q5
tof q2 q7
tof q3 q9
tof q4 q5 q6
tof q7 q6 q8
tof q9 q8 q10
tof q10 q11
tof q9 q8 q10
tof q7 q6 q8
tof q4 q5 q6
tof q0 q4
tof q1 q5
tof q2 q7
tof q3 q9
H q4
H q5
H q7
H q9
tof q4
tof q5
tof q7
tof q9
tof q4 q5 q6
tof q7 q6 q8
Z q8 q9
tof q7 q6 q8
tof q4 q5 q6
tof q4
tof q5
tof q7
tof q9
H q4
H q5
H q7
H q9
END
