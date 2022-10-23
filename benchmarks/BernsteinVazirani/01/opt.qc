# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/BernsteinVazirani/1/circuit.qc):
#   Qubits: 2
#   H: 3
#   Z: 1
#   cnot: 1
#   Depth: 4
#   T depth: 0
# Result (0.169ms):
#   Qubits: 2
#   H: 3
#   Z: 1
#   cnot: 1
#   Depth: 4
#   T depth: 0
.v q0 q1
.i q0 q1
.o q0 q1
BEGIN 
H q0
H q1
Z q1
tof q0 q1
H q0
END
