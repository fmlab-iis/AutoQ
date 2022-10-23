# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/BernsteinVazirani/8/circuit.qc):
#   Qubits: 9
#   H: 17
#   Z: 1
#   cnot: 4
#   Depth: 7
#   T depth: 0
# Result (0.393ms):
#   Qubits: 9
#   H: 17
#   Z: 1
#   cnot: 4
#   Depth: 7
#   T depth: 0
.v q0 q1 q2 q3 q4 q5 q6 q7 q8
.i q0 q1 q2 q3 q4 q5 q6 q7 q8
.o q0 q1 q2 q3 q4 q5 q6 q7 q8
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
Z q8
tof q0 q8
tof q2 q8
tof q4 q8
tof q6 q8
H q0
H q1
H q2
H q3
H q4
H q5
H q6
H q7
END
