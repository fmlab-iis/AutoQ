# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/rd73_140/circuit.qc):
#   Qubits: 10
#   H: 28
#   T: 98
#   cnot: 90
#   Depth: 78
#   T depth: 35
# Result (0.704ms):
#   Qubits: 10
#   H: 28
#   T: 98
#   cnot: 90
#   Depth: 78
#   T depth: 35
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
BEGIN 
tof q0 q1 q7
tof q0 q1
tof q2 q7 q8
tof q1 q2 q7
tof q1 q2
tof q3 q8 q9
tof q3 q7 q8
tof q2 q3 q7
tof q2 q3
tof q4 q8 q9
tof q4 q7 q8
tof q3 q4 q7
tof q3 q4
tof q5 q8 q9
tof q5 q7 q8
tof q4 q5 q7
tof q4 q5
tof q6 q8 q9
tof q5 q6 q7
tof q5 q6
END
