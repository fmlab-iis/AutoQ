# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Grover/6/circuit.qc):
#   Qubits: 12
#   H: 295
#   T: 756
#   X: 109
#   cnot: 654
#   cz: 6
#   Depth: 871
#   T depth: 348
# Result (4.441ms):
#   Qubits: 12
#   H: 295
#   T: 756
#   X: 109
#   cnot: 654
#   cz: 6
#   Depth: 871
#   T depth: 348
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
BEGIN 
tof q11
H q0
H q1
H q3
H q5
H q7
H q9
H q11
tof q7
tof q3
tof q0
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q10 q11
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
Z q8 q9
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
H q0
H q1
H q3
H q5
H q7
H q9
tof q7
tof q3
tof q0
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q10 q11
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
Z q8 q9
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
H q0
H q1
H q3
H q5
H q7
H q9
tof q7
tof q3
tof q0
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q10 q11
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
Z q8 q9
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
H q0
H q1
H q3
H q5
H q7
H q9
tof q7
tof q3
tof q0
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q10 q11
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
Z q8 q9
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
H q0
H q1
H q3
H q5
H q7
H q9
tof q7
tof q3
tof q0
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q10 q11
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
Z q8 q9
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
H q0
H q1
H q3
H q5
H q7
H q9
tof q7
tof q3
tof q0
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
tof q9 q8 q10
tof q10 q11
tof q9 q8 q10
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q7
tof q3
tof q0
H q0
H q1
H q3
H q5
H q7
H q9
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
tof q0 q1 q2
tof q3 q2 q4
tof q5 q4 q6
tof q7 q6 q8
Z q8 q9
tof q7 q6 q8
tof q5 q4 q6
tof q3 q2 q4
tof q0 q1 q2
tof q0
tof q1
tof q3
tof q5
tof q7
tof q9
H q0
H q1
H q3
H q5
H q7
H q9
END
