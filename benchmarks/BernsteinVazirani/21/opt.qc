# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/BernsteinVazirani/21/circuit.qc):
#   Qubits: 22
#   H: 43
#   Z: 1
#   cnot: 11
#   Depth: 14
#   T depth: 0
# Result (0.994ms):
#   Qubits: 22
#   H: 43
#   Z: 1
#   cnot: 11
#   Depth: 14
#   T depth: 0
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21
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
H q14
H q15
H q16
H q17
H q18
H q19
H q20
H q21
Z q21
tof q0 q21
tof q2 q21
tof q4 q21
tof q6 q21
tof q8 q21
tof q10 q21
tof q12 q21
tof q14 q21
tof q16 q21
tof q18 q21
tof q20 q21
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
H q14
H q15
H q16
H q17
H q18
H q19
H q20
END
