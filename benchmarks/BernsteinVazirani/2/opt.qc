# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/BernsteinVazirani/2/circuit.qc):
#   Qubits: 3
#   H: 5
#   Z: 1
#   cnot: 1
#   Depth: 4
#   T depth: 0
# Result (0.275ms):
#   Qubits: 3
#   H: 5
#   Z: 1
#   cnot: 1
#   Depth: 4
#   T depth: 0
.v q0 q1 q2
.i q0 q1 q2
.o q0 q1 q2
BEGIN 
H q0
H q1
H q2
Z q2
tof q0 q2
H q0
H q1
END
