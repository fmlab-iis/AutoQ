# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/BernsteinVazirani/4/circuit.qc):
#   Qubits: 5
#   H: 9
#   Z: 1
#   cnot: 2
#   Depth: 5
#   T depth: 0
# Result (0.354ms):
#   Qubits: 5
#   H: 9
#   Z: 1
#   cnot: 2
#   Depth: 5
#   T depth: 0
.v q0 q1 q2 q3 q4
.i q0 q1 q2 q3 q4
.o q0 q1 q2 q3 q4
BEGIN 
H q0
H q1
H q2
H q3
H q4
Z q4
tof q0 q4
tof q2 q4
H q0
H q1
H q2
H q3
END
