# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/rd32_271/circuit.qc):
#   Qubits: 5
#   H: 10
#   T: 35
#   X: 3
#   cnot: 31
#   Depth: 41
#   T depth: 18
# Result (0.350ms):
#   Qubits: 5
#   H: 10
#   T: 35
#   X: 3
#   cnot: 31
#   Depth: 41
#   T depth: 18
.v q0 q1 q2 q3 q4
.i q0 q1 q2 q3 q4
.o q0 q1 q2 q3 q4
BEGIN 
tof q0 q2 q3
tof q1 q2 q4
tof q1 q2 q3
tof q0 q1 q3
tof q1
tof q2
tof q1 q2 q4
tof q0
tof q0 q4
END
