# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/BernsteinVazirani/23/circuit.qc):
#   Qubits: 24
#   H: 47
#   Z: 1
#   cnot: 12
#   Depth: 15
#   T depth: 0
# Result (1.124ms):
#   Qubits: 24
#   H: 47
#   Z: 1
#   cnot: 12
#   Depth: 15
#   T depth: 0
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23
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
H q22
H q23
Z q23
tof q0 q23
tof q2 q23
tof q4 q23
tof q6 q23
tof q8 q23
tof q10 q23
tof q12 q23
tof q14 q23
tof q16 q23
tof q18 q23
tof q20 q23
tof q22 q23
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
H q22
END
