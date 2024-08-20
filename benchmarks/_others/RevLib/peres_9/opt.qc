# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/peres_9/circuit.qc):
#   Qubits: 3
#   H: 2
#   T: 7
#   cnot: 7
#   Depth: 9
#   T depth: 4
# Result (0.231ms):
#   Qubits: 3
#   H: 2
#   T: 7
#   cnot: 7
#   Depth: 9
#   T depth: 4
.v q0 q1 q2
.i q0 q1 q2
.o q0 q1 q2
BEGIN 
tof q2 q1 q0
tof q2 q1
END
