# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/rd53_311/circuit.qc):
#   Qubits: 13
#   H: 32
#   T: 112
#   X: 6
#   cnot: 108
#   Depth: 110
#   T depth: 49
# Result (0.908ms):
#   Qubits: 13
#   H: 32
#   T: 112
#   X: 6
#   cnot: 108
#   Depth: 110
#   T depth: 49
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
BEGIN 
tof q3 q5
tof q3 q4 q5
tof q4 q5
tof q3 q4 q6
tof q6 q7
tof q0 q5 q7
tof q0 q6 q7
tof q0 q6 q8
tof q8 q9
tof q2 q7 q9
tof q2 q8 q9
tof q2 q8 q10
tof q10 q9
tof q1 q9 q10
tof q3 q11
tof q4 q11
tof q0 q11
tof q11
tof q2 q11
tof q11
tof q1 q11
tof q11
tof q5
tof q0 q5 q6
tof q0 q6 q5
tof q5 q12
tof q2 q7 q12
tof q2 q5 q12
tof q7
tof q2 q7 q5
tof q2 q5 q7
tof q7 q12
tof q1 q12 q7
tof q7
END
