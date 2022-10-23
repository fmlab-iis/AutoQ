# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/BernsteinVazirani/5/circuit.qc):
#   Qubits: 6
#   H: 11
#   Z: 1
#   cnot: 3
#   Depth: 6
#   T depth: 0
# Result (0.455ms):
#   Qubits: 6
#   H: 11
#   Z: 1
#   cnot: 3
#   Depth: 6
#   T depth: 0
.v q0 q1 q2 q3 q4 q5
.i q0 q1 q2 q3 q4 q5
.o q0 q1 q2 q3 q4 q5
BEGIN 
H q0
H q1
H q2
H q3
H q4
H q5
Z q5
tof q0 q5
tof q2 q5
tof q4 q5
H q0
H q1
H q2
H q3
H q4
END
