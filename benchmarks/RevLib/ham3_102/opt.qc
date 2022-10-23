# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/ham3_102/circuit.qc):
#   Qubits: 3
#   H: 2
#   T: 7
#   cnot: 10
#   Depth: 12
#   T depth: 4
# Result (0.218ms):
#   Qubits: 3
#   H: 2
#   T: 7
#   cnot: 10
#   Depth: 12
#   T depth: 4
.v q0 q1 q2
.i q0 q1 q2
.o q0 q1 q2
BEGIN 
tof q1 q2 q0
tof q2 q1
tof q1 q2
tof q0 q2
tof q2 q1
END
