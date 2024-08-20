# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Feynman/tof_5/circuit.qc):
#   Qubits: 9
#   H: 14
#   T: 49
#   cnot: 42
#   Depth: 53
#   T depth: 22
# Result (0.534ms):
#   Qubits: 9
#   H: 14
#   T: 49
#   cnot: 42
#   Depth: 53
#   T depth: 22
.v 1 2 3 4 5 6 7 8 9
.i 1 2 3 4 5 9
.o 1 2 3 4 5 6 7 8 9
BEGIN 
H 6
Z 1 2 6
H 6
H 7
Z 3 6 7
H 7
H 8
Z 4 7 8
H 8
H 9
Z 5 8 9
H 9
H 8
Zd 4 7 8
H 8
H 7
Zd 3 6 7
H 7
H 6
Zd 1 2 6
H 6
END
