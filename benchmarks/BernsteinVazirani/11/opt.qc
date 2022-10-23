# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/BernsteinVazirani/11/circuit.qc):
#   Qubits: 12
#   H: 23
#   Z: 1
#   cnot: 6
#   Depth: 9
#   T depth: 0
# Result (0.739ms):
#   Qubits: 12
#   H: 23
#   Z: 1
#   cnot: 6
#   Depth: 9
#   T depth: 0
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
BEGIN 
H q0
H q1
H q2
H q3
H q4
H q5
H q6
H q7
H q8
H q9
H q10
H q11
Z q11
tof q0 q11
tof q2 q11
tof q4 q11
tof q6 q11
tof q8 q11
tof q10 q11
H q0
H q1
H q2
H q3
H q4
H q5
H q6
H q7
H q8
H q9
H q10
END
