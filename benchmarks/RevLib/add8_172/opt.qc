# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/add8_172/circuit.qc):
#   Qubits: 25
#   H: 32
#   T: 112
#   cnot: 112
#   Depth: 67
#   T depth: 29
# Result (1.078ms):
#   Qubits: 25
#   H: 32
#   T: 112
#   cnot: 112
#   Depth: 67
#   T depth: 29
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24
BEGIN 
tof q24 q23 q21
tof q24 q23
tof q23 q22 q21
tof q23 q22
tof q20 q19 q18
tof q20 q19
tof q19 q21 q18
tof q19 q21
tof q17 q16 q15
tof q17 q16
tof q16 q18 q15
tof q16 q18
tof q14 q13 q12
tof q14 q13
tof q13 q15 q12
tof q13 q15
tof q11 q10 q9
tof q11 q10
tof q10 q12 q9
tof q10 q12
tof q8 q7 q6
tof q8 q7
tof q7 q9 q6
tof q7 q9
tof q5 q4 q3
tof q5 q4
tof q4 q6 q3
tof q4 q6
tof q2 q1 q0
tof q2 q1
tof q1 q3 q0
tof q1 q3
END
