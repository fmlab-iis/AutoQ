# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/sys6-v0_111/circuit.qc):
#   Qubits: 10
#   H: 26
#   T: 91
#   cnot: 85
#   Depth: 64
#   T depth: 28
# Result (0.701ms):
#   Qubits: 10
#   H: 26
#   T: 91
#   cnot: 85
#   Depth: 64
#   T depth: 28
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
BEGIN 
tof q0 q1 q6
tof q0 q1
tof q2 q6 q7
tof q1 q2 q6
tof q1 q2
tof q3 q7 q8
tof q3 q6 q7
tof q2 q3 q6
tof q2 q3
tof q4 q8 q9
tof q4 q7 q8
tof q4 q6 q7
tof q3 q4 q6
tof q3 q4
tof q5 q8 q9
tof q5 q7 q8
tof q4 q5 q6
tof q4 q5
tof q6 q9
tof q8 q9
END
