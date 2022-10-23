# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/sym9_146/circuit.qc):
#   Qubits: 12
#   H: 40
#   T: 140
#   cnot: 128
#   Depth: 106
#   T depth: 49
# Result (0.899ms):
#   Qubits: 12
#   H: 40
#   T: 140
#   cnot: 128
#   Depth: 106
#   T depth: 49
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
BEGIN 
tof q0 q1 q9
tof q0 q1
tof q2 q9 q10
tof q1 q2 q9
tof q1 q2
tof q3 q10 q11
tof q3 q9 q10
tof q2 q3 q9
tof q2 q3
tof q4 q10 q11
tof q4 q9 q10
tof q3 q4 q9
tof q3 q4
tof q5 q10 q11
tof q5 q9 q10
tof q4 q5 q9
tof q4 q5
tof q6 q10 q11
tof q6 q9 q10
tof q5 q6 q9
tof q5 q6
tof q7 q10 q11
tof q7 q9 q10
tof q6 q7 q9
tof q6 q7
tof q8 q10 q11
tof q8 q9 q10
tof q10 q11
END
