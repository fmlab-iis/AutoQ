# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/BernsteinVazirani/13/circuit.qc):
#   Qubits: 14
#   H: 27
#   Z: 1
#   cnot: 7
#   Depth: 10
#   T depth: 0
# Result (0.824ms):
#   Qubits: 14
#   H: 27
#   Z: 1
#   cnot: 7
#   Depth: 10
#   T depth: 0
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
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
H q12
H q13
Z q13
tof q0 q13
tof q2 q13
tof q4 q13
tof q6 q13
tof q8 q13
tof q10 q13
tof q12 q13
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
H q12
END
