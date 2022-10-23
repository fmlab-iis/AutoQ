# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/fredkin_6/circuit.qc):
#   Qubits: 3
#   H: 6
#   T: 21
#   cnot: 18
#   Depth: 24
#   T depth: 12
# Result (0.280ms):
#   Qubits: 3
#   H: 6
#   T: 21
#   cnot: 18
#   Depth: 24
#   T depth: 12
.v q0 q1 q2
.i q0 q1 q2
.o q0 q1 q2
BEGIN 
tof q0 q2 q1
tof q1 q0 q2
tof q0 q2 q1
END
