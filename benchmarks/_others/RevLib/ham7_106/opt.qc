# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/ham7_106/circuit.qc):
#   Qubits: 7
#   H: 12
#   T: 42
#   cnot: 55
#   Depth: 58
#   T depth: 22
# Result (0.410ms):
#   Qubits: 7
#   H: 12
#   T: 42
#   cnot: 55
#   Depth: 58
#   T depth: 22
.v q0 q1 q2 q3 q4 q5 q6
.i q0 q1 q2 q3 q4 q5 q6
.o q0 q1 q2 q3 q4 q5 q6
BEGIN 
tof q4 q5
tof q6 q1
tof q6 q2
tof q4 q5 q6
tof q6 q4
tof q6 q5
tof q3 q2
tof q3 q0
tof q3 q1
tof q2 q5 q3
tof q4 q6 q2
tof q2 q5 q3
tof q3 q1
tof q5 q6 q4
tof q3 q0
tof q3 q5
tof q4 q6 q3
tof q1 q4
tof q2 q1
tof q3 q6
tof q2 q5
tof q1 q3
tof q3 q0
tof q0 q3
tof q0 q2
END
