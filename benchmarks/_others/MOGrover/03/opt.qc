# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/MOGrover/03/circuit.qc):
#   Qubits: 9
#   H: 41
#   T: 84
#   X: 19
#   cnot: 86
#   cz: 2
#   Depth: 111
#   T depth: 44
# Result (2.110ms):
#   Qubits: 9
#   H: 41
#   T: 84
#   X: 19
#   cnot: 86
#   cz: 2
#   Depth: 111
#   T depth: 44
.v q0 q1 q2 q3 q4 q5 q6 q7 q8
.i q0 q1 q2 q3 q4 q5 q6 q7 q8
.o q0 q1 q2 q3 q4 q5 q6 q7 q8
BEGIN 
tof q8
tof q0
tof q1
tof q2
H q3
H q4
H q6
H q8
tof q0 q3
tof q1 q4
tof q2 q6
tof q3 q4 q5
tof q6 q5 q7
tof q7 q8
tof q6 q5 q7
tof q3 q4 q5
tof q0 q3
tof q1 q4
tof q2 q6
H q3
H q4
H q6
tof q3
tof q4
tof q6
tof q3 q4 q5
Z q5 q6
tof q3 q4 q5
tof q3
tof q4
tof q6
H q3
H q4
H q6
tof q0 q3
tof q1 q4
tof q2 q6
tof q3 q4 q5
tof q6 q5 q7
tof q7 q8
tof q6 q5 q7
tof q3 q4 q5
tof q0 q3
tof q1 q4
tof q2 q6
H q3
H q4
H q6
tof q3
tof q4
tof q6
tof q3 q4 q5
Z q5 q6
tof q3 q4 q5
tof q3
tof q4
tof q6
H q3
H q4
H q6
tof q0
tof q1
tof q2
H q8
END
