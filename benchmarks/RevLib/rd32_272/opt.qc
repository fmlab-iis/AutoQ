# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/rd32_272/circuit.qc):
#   Qubits: 5
#   H: 6
#   T: 21
#   cnot: 21
#   Depth: 26
#   T depth: 11
# Result (0.304ms):
#   Qubits: 5
#   H: 6
#   T: 21
#   cnot: 21
#   Depth: 26
#   T depth: 11
.v q0 q1 q2 q3 q4
.i q0 q1 q2 q3 q4
.o q0 q1 q2 q3 q4
BEGIN 
tof q0 q1 q4
tof q0 q2 q4
tof q1 q2 q4
tof q0 q3
tof q1 q3
tof q2 q3
END
