# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Feynman/tof_4/circuit.qc):
#   Qubits: 7
#   H: 10
#   T: 35
#   cnot: 30
#   Depth: 38
#   T depth: 16
# Result (0.516ms):
#   Qubits: 7
#   H: 10
#   T: 35
#   cnot: 30
#   Depth: 38
#   T depth: 16
.v 1 2 3 4 5 6 7
.i 1 2 3 4 7
.o 1 2 3 4 5 6 7
BEGIN 
H 5
Z 1 2 5
H 5
H 6
Z 3 5 6
H 6
H 7
Z 4 6 7
H 7
H 6
Zd 3 5 6
H 6
H 5
Zd 1 2 5
H 5
END
