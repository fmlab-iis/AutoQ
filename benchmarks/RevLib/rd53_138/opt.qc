# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/rd53_138/circuit.qc):
#   Qubits: 8
#   H: 16
#   T: 56
#   cnot: 52
#   Depth: 48
#   T depth: 21
# Result (0.496ms):
#   Qubits: 8
#   H: 16
#   T: 56
#   cnot: 52
#   Depth: 48
#   T depth: 21
.v q0 q1 q2 q3 q4 q5 q6 q7
.i q0 q1 q2 q3 q4 q5 q6 q7
.o q0 q1 q2 q3 q4 q5 q6 q7
BEGIN 
tof q0 q1 q5
tof q0 q1
tof q2 q5 q6
tof q1 q2 q5
tof q1 q2
tof q3 q6 q7
tof q3 q5 q6
tof q2 q3 q5
tof q2 q3
tof q4 q6 q7
tof q3 q4 q5
tof q3 q4
END
