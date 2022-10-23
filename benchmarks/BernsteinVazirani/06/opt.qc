# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/BernsteinVazirani/6/circuit.qc):
#   Qubits: 7
#   H: 13
#   Z: 1
#   cnot: 3
#   Depth: 6
#   T depth: 0
# Result (0.351ms):
#   Qubits: 7
#   H: 13
#   Z: 1
#   cnot: 3
#   Depth: 6
#   T depth: 0
.v q0 q1 q2 q3 q4 q5 q6
.i q0 q1 q2 q3 q4 q5 q6
.o q0 q1 q2 q3 q4 q5 q6
BEGIN 
H q0
H q1
H q2
H q3
H q4
H q5
H q6
Z q6
tof q0 q6
tof q2 q6
tof q4 q6
H q0
H q1
H q2
H q3
H q4
H q5
END
