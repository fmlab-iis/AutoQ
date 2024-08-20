# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/mini_alu_305/circuit.qc):
#   Qubits: 10
#   H: 20
#   T: 70
#   X: 3
#   cnot: 67
#   Depth: 60
#   T depth: 26
# Result (0.725ms):
#   Qubits: 10
#   H: 20
#   T: 70
#   X: 3
#   cnot: 67
#   Depth: 60
#   T depth: 26
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
BEGIN 
tof q1 q2 q4
tof q3 q4 q5
tof q1 q2 q6
tof q2 q6
tof q6
tof q0 q6 q5
tof q0 q5 q6
tof q1 q7
tof q2 q7
tof q3 q8
tof q4 q8
tof q3 q7 q8
tof q3 q4 q8
tof q3 q9
tof q3 q4 q9
tof q4 q9
tof q9
tof q0 q9 q8
tof q0 q8 q9
tof q9
END
