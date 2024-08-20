# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/MCToffoli/6/circuit.qc):
#   Qubits: 12
#   H: 20
#   T: 70
#   cnot: 61
#   Depth: 77
#   T depth: 32
# Result (0.442ms):
#   Qubits: 12
#   H: 20
#   T: 70
#   cnot: 61
#   Depth: 77
#   T depth: 32
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
BEGIN 
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
END
